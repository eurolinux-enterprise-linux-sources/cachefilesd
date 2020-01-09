/* CacheFiles userspace management daemon
 *
 * Copyright (C) 2006-2007 Red Hat, Inc. All Rights Reserved.
 * Written by David Howells (dhowells@redhat.com)
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version
 * 2 of the License, or (at your option) any later version.
 *
 *
 * Configuration file goes in /etc/cachefiles.conf and is of the form:
 *
 *	dir /var/cache/fscache
 *	tag mycache
 *	brun 10%
 *	bcull 7%
 *	bstop 3%
 *	frun 10%
 *	fcull 7%
 *	fstop 3%
 *
 * Only "dir" is mandatory
 * Blank lines and lines beginning with a hash are comments
 * Trailing spaces are significant
 * There is no character escaping mechanism
 * NUL characters are cause for error
 */

#define CACHEFILESD_VERSION "0.10.7"

#define _GNU_SOURCE
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <signal.h>
#include <syslog.h>
#include <unistd.h>
#include <fcntl.h>
#include <ctype.h>
#include <errno.h>
#include <getopt.h>
#include <syslog.h>
#include <dirent.h>
#include <time.h>
#include <poll.h>
#include <limits.h>
#include <grp.h>
#include <sys/inotify.h>
#include <sys/time.h>
#include <sys/vfs.h>
#include <sys/stat.h>

typedef enum objtype {
	OBJTYPE_INDEX,
	OBJTYPE_DATA,
	OBJTYPE_SPECIAL,
	OBJTYPE_INTERMEDIATE,
} objtype_t;

struct object {
	struct object	*parent;	/* parent dir of this object (or NULL) */
	struct object	*children;	/* children of this object */
	struct object	*next;		/* next child of parent */
	struct object	*prev;		/* previous child of parent */
	DIR		*dir;		/* this object's directory (or NULL for data obj) */
	ino_t		ino;		/* inode number of this object */
	int		usage;		/* number of users of this object */
	bool		empty;		/* T if directory empty */
	bool		new;		/* T if object new */
	bool		cullable;	/* T if object now cullable */
	objtype_t	type;		/* type of object */
	time_t		atime;		/* last access time on this object */
	char		name[1];	/* name of this object */
};

/* cache root representation */
static struct object root = {
	.parent		= NULL,
	.usage		= 2,
	.type		= OBJTYPE_INDEX,
};

static int nobjects = 1;
static int nopendir;

/* current scan point */
static struct object *scan_cursor;
static bool scan_signalled, stop_signalled, reap_signalled;

/* ranked order of cullable objects
 * - we have two tables: one we're building and one that's full of ready to be
 *   culled objects
 */
static unsigned culltable_size = 4096;
static struct object **cullbuild;
static struct object **cullready;

static unsigned nr_in_build_table;
static unsigned nr_in_ready_table;
static int ncullable;
static bool kernel_wants_cull;
static bool have_nr_releases;
static unsigned long long f_released_since_last_scan;
static unsigned long long b_released_since_last_scan;


static const char *configfile = "/etc/cachefilesd.conf";
static const char *devfile = "/dev/cachefiles";
static const char *procfile = "/proc/fs/cachefiles";
static const char *pidfile = "/var/run/cachefilesd.pid";
static char *cacheroot, *graveyardpath;

static bool culling_disabled;
static bool xnolog, xopenedlog;
static int xdebug;
static int graveyardfd;
static unsigned long long brun, bcull, bstop, frun, fcull, fstop;
static unsigned long long b_resume_threshold = ULLONG_MAX;
static unsigned long long f_resume_threshold = 5;

static const gid_t group_list[0];

#define cachefd 3

static __attribute__((noreturn))
void version(void)
{
	printf("cachefilesd version " CACHEFILESD_VERSION "\n");
	exit(0);
}

static __attribute__((noreturn))
void help(void)
{
	fprintf(stderr,
		"Format:\n"
		"  /sbin/cachefilesd [-d]* [-s] [-n] [-p <pidfile>] [-f <configfile>]\n"
		"  /sbin/cachefilesd -v\n"
		"\n"
		"Options:\n"
		"  -d\tIncrease debugging level (cumulative)\n"
		"  -n\tDon't daemonise the process\n"
		"  -s\tMessage output to stderr instead of syslog\n"
		"  -p <pidfile>\tWrite the PID into the file\n"
		"  -f <configfile>\n"
		"  -v\tPrint version and exit\n"
		"\tRead the specified configuration file instead of"
		" /etc/cachefiles.conf\n");

	exit(2);
}

static __attribute__((noreturn, format(printf, 2, 3)))
void __error(int excode, const char *fmt, ...)
{
	va_list va;

	if (xnolog) {
		va_start(va, fmt);
		vfprintf(stderr, fmt, va);
		va_end(va);
	}
	else {
		if (!xopenedlog) {
			openlog("cachefilesd", LOG_PID, LOG_DAEMON);
			xopenedlog = true;
		}

		va_start(va, fmt);
		vsyslog(LOG_ERR, fmt, va);
		va_end(va);

		closelog();
	}

	exit(excode);
}

#define error(FMT,...)		__error(3, "Internal error: "FMT"\n" ,##__VA_ARGS__)
#define oserror(FMT,...)	__error(1, FMT": errno %d (%m)\n" ,##__VA_ARGS__ ,errno)
#define cfgerror(FMT,...)	__error(2, "%s:%d:"FMT"\n", configfile, lineno ,##__VA_ARGS__)
#define opterror(FMT,...)	__error(2, FMT"\n" ,##__VA_ARGS__)

static __attribute__((format(printf, 3, 4)))
void __message(int dlevel, int level, const char *fmt, ...)
{
	va_list va;

	if (dlevel <= xdebug) {
		if (xnolog) {
			va_start(va, fmt);
			vfprintf(stderr, fmt, va);
			va_end(va);
		}
		else if (!xnolog) {
			if (!xopenedlog) {
				openlog("cachefilesd", LOG_PID, LOG_DAEMON);
				xopenedlog = true;
			}

			va_start(va, fmt);
			vsyslog(level, fmt, va);
			va_end(va);

			closelog();
		}
	}
}

#define info(FMT,...)		__message(0,  LOG_INFO,   FMT"\n" ,##__VA_ARGS__)
#define debug(DL, FMT,...)	__message(DL, LOG_DEBUG,  FMT"\n" ,##__VA_ARGS__)
#define notice(FMT,...)		__message(0,  LOG_NOTICE, FMT"\n" ,##__VA_ARGS__)

static void open_cache(void);
static void cachefilesd(void) __attribute__((noreturn));
static void reap_graveyard(void);
static void reap_graveyard_aux(const char *dirname);
static void read_cache_state(void);
static int is_object_in_use(const char *filename);
static void cull_file(const char *filename);
static void begin_building_cull_table(void);
static bool build_cull_table(void);
static void decant_cull_table(void);
static void insert_into_cull_table(struct object *object);
static void put_object(struct object *object);
static struct object *create_object(struct object *parent, const char *name, struct stat64 *st);
static void destroy_unexpected_object(struct object *parent, struct dirent *de);
static int get_dir_fd(struct object *dir);
static void cull_object(struct object *object);
static void cull_objects(void);

/*****************************************************************************/
/*
 * termination request
 */
static void sigterm(int sig)
{
	stop_signalled = true;
}

/*****************************************************************************/
/*
 * the graveyard was populated
 */
static void sigio(int sig)
{
	reap_signalled = true;
}

/*****************************************************************************/
/*
 * redo scan after a time since the last scan turned up no results
 */
static void sigalrm(int sig)
{
	scan_signalled = true;
}

/*****************************************************************************/
/*
 * write the PID file
 */
static void write_pidfile(void)
{
	FILE *pf;

	pf = fopen(pidfile, "w");
	if (!pf)
		oserror("Unable to open PID file: %s", pidfile);

	if (fprintf(pf, "%d\n", getpid()) < 0 ||
	    fclose(pf) == EOF)
		oserror("Unable to write PID file: %s", pidfile);
}

/*****************************************************************************/
/*
 * start up the cache and go
 */
int main(int argc, char *argv[])
{
	struct stat st;
	unsigned lineno;
	ssize_t n;
	size_t m;
	FILE *config;
	char *line, *cp;
	long page_size;
	int _cachefd, nullfd, opt, loop, open_max;
	bool nodaemon = false;

	/* handle help request */
	if (argc == 2 && strcmp(argv[1], "--help") == 0)
		help();

	if (argc == 2 && strcmp(argv[1], "--version") == 0)
		version();

	/* parse the arguments */
	while (opt = getopt(argc, argv, "dsnNf:p:v"),
	       opt != EOF
	       ) {
		switch (opt) {
		case 'd':
			/* turn on debugging */
			xdebug++;
			break;

		case 's':
			/* disable syslog writing */
			xnolog = true;
			break;

		case 'n':
			/* don't daemonise */
			nodaemon = true;
			break;

		case 'N':
			/* disable culling */
			culling_disabled = true;
			break;

		case 'f':
			/* use a specific config file */
			configfile = optarg;
			break;

		case 'p':
			/* use a specific PID file */
			pidfile = optarg;
			break;

		case 'v':
			/* print the version and exit */
			version();

		default:
			opterror("Unknown commandline option '%c'", optopt);
		}
	}

	/* read various parameters */
	page_size = sysconf(_SC_PAGESIZE);
	if (page_size < 0)
		oserror("Unable to get page size");

	open_max = sysconf(_SC_OPEN_MAX);
	if (open_max < 0)
		oserror("Unable to get max open files");

	/* become owned by root */
	if (setgroups(sizeof(group_list) / sizeof(gid_t), group_list) < 0)
		oserror("Unable to clear the supplementary groups");

	if (setresuid(0, 0, 0) < 0)
		oserror("Unable to set UID to 0");

	if (setresgid(0, 0, 0) < 0)
		oserror("Unable to set GID to 0");

	/* just in case... */
	sync();

	/* open the devfile or the procfile on fd 3 */
	_cachefd = open(devfile, O_RDWR);
	if (_cachefd < 0) {
		if (errno != ENOENT)
			oserror("Unable to open %s", devfile);

		_cachefd = open(procfile, O_RDWR);
		if (_cachefd < 0) {
			if (errno == ENOENT)
				oserror("Unable to open %s", devfile);
			oserror("Unable to open %s", procfile);
		}
	}

	if (_cachefd != cachefd) {
		if (dup2(_cachefd, cachefd) < 0)
			oserror("Unable to transfer cache fd to 3");
		if (close(_cachefd) < 0)
			oserror("Close of original cache fd failed");
	}

	/* open /dev/null */
	nullfd = open("/dev/null", O_RDWR);
	if (nullfd < 0)
		oserror("Unable to open /dev/null");

	/* open the config file */
	config = fopen(configfile, "r");
	if (!config)
		oserror("Unable to open %s", configfile);

	/* read the configuration */
	m = 0;
	line = NULL;
	lineno = 0;
	while (n = getline(&line, &m, config),
	       n != EOF
	       ) {
		lineno++;

		if (n >= page_size)
			cfgerror("Line too long");

		if (memchr(line, 0, n) != 0)
			cfgerror("Line contains a NUL character");

		/* eat blank lines, leading white space and trailing NL */
		cp = strchr(line, '\n');
		if (!cp)
			cfgerror("Unterminated line");

		if (cp == line)
			continue;
		*cp = '\0';

		for (cp = line; isspace(*cp); cp++) {;}

		if (!*cp)
			continue;

		/* eat full line comments */
		if (*cp == '#')
			continue;

		/*  allow culling to be disabled */
		if (memcmp(cp, "nocull", 6) == 0 &&
		    (!cp[6] || isspace(cp[6]))) {
			culling_disabled = true;
		}

		/* note the cull table size command */
		if (memcmp(cp, "culltable", 9) == 0 && isspace(cp[9])) {
			unsigned long cts;
			char *sp;

			for (sp = cp + 10; isspace(*sp); sp++) {;}

			cts = strtoul(sp, &sp, 10);
			if (*sp)
				cfgerror("Invalid cull table size number");
			if (cts < 12 || cts > 20)
				cfgerror("Log2 of cull table size must be 12 <= N <= 20");
			culltable_size = 1 << cts;
			continue;
		}

		/* Note the suspension resume released file count thresholds
		 * ("-" to disable a threshold).
		 */
		if (memcmp(cp, "resume_thresholds", 18) == 0 && isspace(cp[18])) {
			unsigned long long b_thresh, f_thresh;
			char *sp;

			for (sp = cp + 18; isspace(*sp); sp++) {;}

			if (*sp == '-') {
				sp++;
				b_thresh = ULLONG_MAX;
			} else {
				b_thresh = strtoul(sp, &sp, 10);
			}

			if (!*sp || !isspace(*sp))
				cfgerror("Error parsing resume threshold (blocks)");
			if (b_thresh == 0)
				cfgerror("Invalid resume threshold (blocks)");
			for (; isspace(*sp); sp++) {;}

			if (*sp == '-') {
				sp++;
				f_thresh = ULLONG_MAX;
			} else {
				f_thresh = strtoul(sp, &sp, 10);
				if (*sp)
					cfgerror("Error parsing resume threshold (files)");
				if (f_thresh == 0)
					cfgerror("Invalid resume threshold (files)");
			}

			b_resume_threshold = b_thresh;
			f_resume_threshold = f_thresh;
			continue;
		}

		/* note the dir command */
		if (memcmp(cp, "dir", 3) == 0 && isspace(cp[3])) {
			char *sp;

			for (sp = cp + 4; isspace(*sp); sp++) {;}

			if (strlen(sp) > PATH_MAX - 10)
				cfgerror("Cache pathname is too long");

			if (stat(sp, &st) < 0)
				oserror("Can't confirm cache location");

			cacheroot = strdup(sp);
			if (!cacheroot)
				oserror("Can't copy cache name");
		}

		/* object to the bind command */
		if (memcmp(cp, "bind", 4) == 0 &&
		    (!cp[4] || isspace(cp[4])))
			cfgerror("'bind' command not permitted");

		/* pass the config options over to the kernel module */
		if (write(cachefd, line, strlen(line)) < 0) {
			if (errno == -ENOMEM || errno == -EIO)
				oserror("CacheFiles");
			cfgerror("CacheFiles gave config error: %m");
		}
	}

	if (line)
		free(line);

	if (!feof(config))
		oserror("Unable to read %s", configfile);

	if (fclose(config) == EOF)
		oserror("Unable to close %s", configfile);

	/* allocate the cull tables */
	if (!culling_disabled) {
		cullbuild = calloc(culltable_size, sizeof(cullbuild[0]));
		if (!cullbuild)
			oserror("calloc");

		cullready = calloc(culltable_size, sizeof(cullready[0]));
		if (!cullready)
			oserror("calloc");
	}

	/* leave stdin, stdout, stderr and cachefd open only */
	if (nullfd != 0)
		dup2(nullfd, 0);
	if (nullfd != 1)
		dup2(nullfd, 1);

	for (loop = 4; loop < open_max; loop++)
		close(loop);

	/* set up a connection to syslog whilst we still can (the bind command
	 * will give us our own namespace with no /dev/log */
	openlog("cachefilesd", LOG_PID, LOG_DAEMON);
	xopenedlog = true;
	info("About to bind cache");

	/* now issue the bind command */
	if (write(cachefd, "bind", 4) < 0)
		oserror("CacheFiles bind failed");

	info("Bound cache");

	/* we now have a live cache - daemonise the process */
	if (!nodaemon) {
		if (!xdebug)
			dup2(1, 2);

		switch (fork()) {
		case -1:
			oserror("fork");

		case 0:
			if (xdebug)
				fprintf(stderr, "Daemon PID %d\n", getpid());

			signal(SIGTTIN, SIG_IGN);
			signal(SIGTTOU, SIG_IGN);
			signal(SIGTSTP, SIG_IGN);
			setsid();
			write_pidfile();
			cachefilesd();

		default:
			break;
		}
	}
	else {
		cachefilesd();
	}

	exit(0);
}

/*****************************************************************************/
/*
 * open the cache directories
 */
static void open_cache(void)
{
	struct statfs sfs;
	char buffer[PATH_MAX + 1];

	/* open the cache directory so we can scan it */
	snprintf(buffer, PATH_MAX, "%s/cache", cacheroot);

	root.dir = opendir(buffer);
	if (!root.dir)
		oserror("Unable to open cache directory");
	nopendir++;

	/* open the graveyard so we can set a notification on it */
	if (asprintf(&graveyardpath, "%s/graveyard", cacheroot) < 0)
		oserror("Unable to copy graveyard name");

	graveyardfd = open(graveyardpath, O_DIRECTORY);
	if (graveyardfd < 0)
		oserror("Unable to open graveyard directory");

	if (fstatfs(graveyardfd, &sfs) < 0)
		oserror("Unable to stat cache filesystem");

	if (sfs.f_bsize  + 1 == 0 ||
	    sfs.f_blocks + 1 == 0 ||
	    sfs.f_bfree  + 1 == 0 ||
	    sfs.f_bavail + 1 == 0)
		error("Backing filesystem returns unusable statistics through fstatfs()");
}

/*****************************************************************************/
/*
 * manage the cache
 */
static void cachefilesd(void)
{
	sigset_t sigs, osigs;
	bool scanning_suspended = false;
	bool scan_in_progress = false;

	struct pollfd pollfds[1] = {
		[0] = {
			.fd	= cachefd,
			.events	= POLLIN,
		},
	};

	notice("Daemon Started");

	/* open the cache directories */
	open_cache();

	/* We need to be able to disable signals that we need to check for
	 * before calling poll so that we don't race and miss something.
	 */
	sigemptyset(&sigs);
	sigaddset(&sigs, SIGIO);
	sigaddset(&sigs, SIGINT);
	sigaddset(&sigs, SIGTERM);
	sigaddset(&sigs, SIGALRM);

	signal(SIGTERM, sigterm);
	signal(SIGINT, sigterm);

	/* check the graveyard for graves */
	reap_graveyard();

	while (!stop_signalled) {
		bool do_cull = false;

		debug(3, "Loop %sbuild=%d ready=%d susp=%u scan=%u",
		      culling_disabled ? "NOCULL " : "",
		      nr_in_build_table, nr_in_ready_table,
		      scanning_suspended, scan_in_progress);

		read_cache_state();

		if (!culling_disabled) {
			/* Determine if we're going to need to start a new scan
			 * to refill the cull table.  We want to do this if the
			 * secondary cull table is less than half full - but
			 * overriding that, we don't want to do this if we know
			 * there's insufficient cullables to make it worth
			 * while.
			 */
			if (!scan_in_progress) {
				bool begin_scan = false;

				debug(1, "Consider scan %d/%d",
				      nr_in_build_table, culltable_size / 2);

				if (nr_in_build_table < culltable_size / 2) {
					debug(1, "Want to scan");
					begin_scan = true;
				}

				if (begin_scan && scanning_suspended) {
					debug(1, "Scanning suspended");
					if (have_nr_releases) {
						if (f_released_since_last_scan <
						    f_resume_threshold &&
						    b_released_since_last_scan <
						    b_resume_threshold)
							begin_scan = false;
					} else {
						begin_scan = scan_signalled;
					}
				}

				if (begin_scan) {
					debug(1, "Beginning a scan");
					begin_building_cull_table();
					scan_in_progress = true;
					scanning_suspended = false;
					scan_signalled = false;
					f_released_since_last_scan = 0;
					b_released_since_last_scan = 0;
				}
			}

			/* Determine if there's anything we can actually cull yet if
			 * the kernel is calling for space.
			 */
			if (kernel_wants_cull) {
				debug(1, "Want to cull");
				if (nr_in_ready_table > 0)
					do_cull = true;
			}
		}

		/* We block the signals across the checks for reap, cull and
		 * scan initiation before polling so that we sleep without
		 * racing against the signal handlers.
		 */
		if (!scan_in_progress && !reap_signalled && !do_cull) {
			if (sigprocmask(SIG_BLOCK, &sigs, &osigs) < 0)
				oserror("Unable to block signals");

			if (!reap_signalled &&
			    !stop_signalled &&
			    !scan_signalled) {
				debug(1, "Poll");
				if (ppoll(pollfds, 1, NULL, &osigs) < 0 &&
				    errno != EINTR)
					oserror("Unable to suspend process");
			}

			if (sigprocmask(SIG_UNBLOCK, &sigs, NULL) < 0)
				oserror("Unable to unblock signals");
			continue;
		}

		if (!culling_disabled) {
			if (do_cull)
				cull_objects();

			if (scan_in_progress) {
				scan_in_progress = build_cull_table();
				if (!scan_in_progress) {
					/* Scan complete.
					 *
					 * If the scan didn't produce a full
					 * table then don't repeat the scan
					 * until something gets released by the
					 * kernel.
					 */
					if (nr_in_build_table < culltable_size) {
						debug(1, "Suspend scanning");
						scanning_suspended = true;
						if (!have_nr_releases) {
							signal(SIGALRM, sigalrm);
							alarm(30);
						}
					}
				}
			}

			if (!scan_in_progress) {
				if (nr_in_ready_table <= culltable_size / 2 + 2 &&
				    nr_in_build_table > 0) {
					debug(1, "Decant");
					decant_cull_table();
				}
			}
		}

		if (reap_signalled)
			reap_graveyard();
	}

	notice("Daemon Terminated");
	exit(0);
}

/*****************************************************************************/
/*
 * check the graveyard directory for graves to delete
 */
static void reap_graveyard(void)
{
	/* set a one-shot notification to catch more graves appearing */
	reap_signalled = false;
	signal(SIGIO, sigio);
	if (fcntl(graveyardfd, F_NOTIFY, DN_CREATE) < 0)
		oserror("unable to set notification on graveyard");

	reap_graveyard_aux(graveyardpath);
}

/*****************************************************************************/
/*
 * recursively remove dead stuff from the graveyard
 */
static void reap_graveyard_aux(const char *dirname)
{
	struct dirent dirent, *de;
	bool deleted;
	DIR *dir;
	int ret;

	if (chdir(dirname) < 0)
		oserror("chdir failed");

	dir = opendir(".");
	if (!dir)
		oserror("Unable to open grave dir %s", dirname);

	do {
		/* removing directory entries may cause us to skip when reading
		 * them */
		rewinddir(dir);
		deleted = false;

		while (ret = readdir_r(dir, &dirent, &de),
		       ret == 0 && de != NULL
		       ) {
			/* ignore "." and ".." */
			if (dirent.d_name[0] == '.') {
				if (dirent.d_name[1] == '\0')
					continue;
				if (dirent.d_name[1] == '.' ||
				    dirent.d_name[1] == '\0')
					continue;
			}

			deleted = true;

			/* attempt to unlink non-directory files */
			if (dirent.d_type != DT_DIR) {
				debug(1, "unlink %s", dirent.d_name);
				if (unlink(dirent.d_name) == 0)
					continue;
				if (errno != EISDIR)
					oserror("Unable to unlink file %s",
						dirent.d_name);
			}

			/* recurse into directories */
			memcpy(&dirent, de, sizeof(dirent));

			reap_graveyard_aux(dirent.d_name);

			/* which we then attempt to remove */
			debug(1, "rmdir %s", dirent.d_name);
			if (rmdir(dirent.d_name) < 0)
				oserror("Unable to remove dir %s", dirent.d_name);
		}

		if (ret < 0)
			oserror("Unable to read dir %s", dirname);
	} while (deleted);

	closedir(dir);

	if (chdir("..") < 0)
		oserror("Unable to chdir to ..");
}

/*****************************************************************************/
/*
 * read the cache state
 */
static void read_cache_state(void)
{
	char buffer[4096 + 1], *tok, *next, *arg;
	int n;

	n = read(cachefd, buffer, sizeof(buffer) - 1);
	if (n < 0)
		oserror("Unable to read cache state");
	buffer[n] = '\0';

	debug(3, "KERNEL: %s", buffer);

	tok = buffer;
	do {
		next = strpbrk(tok, " \t");
		if (next)
			*next++ = '\0';

		arg = strchr(tok, '=');
		if (arg) {
			*arg++ = '\0';
		} else {
			debug(0, "Warning: malformed output from kernel, missing arg to [%s]", tok);
			continue;
		}

		if (strcmp(tok, "cull") == 0) {
			kernel_wants_cull = (strtoul(arg, NULL, 0) != 0);
		} else if (strcmp(tok, "brun") == 0) {
			brun = strtoull(arg, NULL, 16);
		} else if (strcmp(tok, "bcull") == 0) {
			bcull = strtoull(arg, NULL, 16);
		} else if (strcmp(tok, "bstop") == 0) {
			bstop = strtoull(arg, NULL, 16);
		} else if (strcmp(tok, "frun") == 0) {
			frun = strtoull(arg, NULL, 16);
		} else if (strcmp(tok, "fcull") == 0) {
			fcull = strtoull(arg, NULL, 16);
		} else if (strcmp(tok, "fstop") == 0) {
			fstop = strtoull(arg, NULL, 16);
		} else if (strcmp(tok, "breleased") == 0) {
			b_released_since_last_scan += strtoull(arg, NULL, 16);
			have_nr_releases = true;
		} else if (strcmp(tok, "freleased") == 0) {
			f_released_since_last_scan += strtoull(arg, NULL, 16);
			have_nr_releases = true;
		}

	} while ((tok = next));
}

/*****************************************************************************/
/*
 * find out if an object in the current working directory is in use
 */
static int is_object_in_use(const char *filename)
{
	char buffer[NAME_MAX + 30];
	int ret, n;

	n = sprintf(buffer, "inuse %s", filename);

	/* command the module */
	ret = write(cachefd, buffer, n);
	if (ret < 0 && errno != ESTALE && errno != ENOENT && errno != EBUSY)
		oserror("Failed to check object's in-use state");

	return ret < 0 && errno == EBUSY ? 1 : 0;
}

/*****************************************************************************/
/*
 * cull a file representing an object in the current working directory
 * - requests CacheFiles rename the object "<cwd>/filename" to the graveyard
 */
static void cull_file(const char *filename)
{
	char buffer[NAME_MAX + 30];
	int ret, n;

	n = sprintf(buffer, "cull %s", filename);

	/* command the module */
	ret = write(cachefd, buffer, n);
	if (ret < 0 && errno != ESTALE && errno != ENOENT && errno != EBUSY)
		oserror("Failed to cull object");
}

/*****************************************************************************/
/*
 * create an object from a name and stat details and attach to the parent, if
 * it doesn't already exist
 */
static struct object *create_object(struct object *parent,
				    const char *name,
				    struct stat64 *st)
{
	struct object *object, *p, *pr;
	int len;

	/* see if the parent object already holds a representation of this
	 * one */
	pr = NULL;
	for (p = parent->children; p; pr = p, p = p->next) {
		if (p->ino <= st->st_ino) {
			if (p->ino == st->st_ino) {
				/* it does */
				p->usage++;
				return p;
			}

			break;
		}
	}

	/* allocate the object
	 * - note that struct object reserves space for NUL directly
	 */
	len = strlen(name);

	object = calloc(1, sizeof(struct object) + len);
	if (!object)
		oserror("Unable to alloc object");

	object->usage = 1;
	object->new = true;

	object->ino = st->st_ino;
	object->atime = st->st_atime;
	memcpy(object->name, name, len + 1);

	switch (object->name[0]) {
	case 'I':
	case 'J':
		object->type = OBJTYPE_INDEX;
		break;
	case 'D':
	case 'E':
		object->type = OBJTYPE_DATA;
		break;
	case 'S':
	case 'T':
		object->type = OBJTYPE_SPECIAL;
		break;
	case '+':
	case '@':
		object->type = OBJTYPE_INTERMEDIATE;
		break;
	default:
		error("Unexpected file type '%c'", object->name[0]);
	}

	/* link into the parent's list */
	parent->usage++;
	object->parent = parent;
	object->prev = pr;
	object->next = p;
	if (pr)
		pr->next = object;
	else
		parent->children = object;
	if (p)
		p->prev = object;

	nobjects++;
	return object;
}

/*****************************************************************************/
/*
 * free up an object, unlinking it from its parent
 */
static void put_object(struct object *object)
{
	struct object *parent;

	if (--object->usage > 0)
		return;

	nobjects--;

	if (object->cullable)
		ncullable--;

	/* destroy the object */
	if (object == &root)
		error("Can't destroy root object representation");

	if (object->children)
		error("Destroying object with children: '%s'", object->name);

	if (object->dir) {
		closedir(object->dir);
		nopendir--;
	}

	if (object->prev)
		object->prev->next = object->next;
	else
		object->parent->children = object->next;

	if (object->next)
		object->next->prev = object->prev;

	parent = object->parent;

	memset(object, 0x6d, sizeof(struct object));
	free(object);

	if (parent)
		put_object(parent);
}

/*****************************************************************************/
/*
 * destroy an unexpected object
 */
static void destroy_unexpected_object(struct object *parent, struct dirent *de)
{
	static unsigned uniquifier;
	struct timeval tv;
	char namebuf[40];
	int fd;

	fd = dirfd(parent->dir);

	if (de->d_type != DT_DIR) {
		if (unlinkat(fd, de->d_name, 0) < 0 &&
		    errno != ENOENT)
			oserror("Unable to unlink unexpectedly named file: %s",
				de->d_name);
	}
	else {
		gettimeofday(&tv, NULL);
		sprintf(namebuf, "x%lxx%xx", tv.tv_sec, uniquifier++);

		if (renameat(fd, de->d_name, graveyardfd, namebuf) < 0 &&
		    errno != ENOENT)
			oserror("Unable to rename unexpectedly named file: %s",
				de->d_name);
	}
}

/*****************************************************************************/
/*
 * insert an object into the cull table if its old enough
 */
static void insert_into_cull_table(struct object *object)
{
	int y, o, m;

	if (!object)
		error("NULL object pointer");

	/* just insert if table is empty */
	if (nr_in_build_table == 0) {
		object->usage++;
		cullbuild[0] = object;
		nr_in_build_table++;
		return;
	}

	/* insert somewhere if table is not full */
	if (nr_in_build_table < culltable_size) {
		object->usage++;

		/* just insert at end if new oldest object */
		if (object->atime <= cullbuild[nr_in_build_table - 1]->atime) {
			cullbuild[nr_in_build_table] = object;
			nr_in_build_table++;
			return;
		}

		/* insert at front if new newest object */
		if (object->atime > cullbuild[0]->atime) {
			memmove(&cullbuild[1],
				&cullbuild[0],
				nr_in_build_table * sizeof(cullbuild[0]));

			cullbuild[0] = object;
			nr_in_build_table++;
			return;
		}

		/* if only two objects in list then insert between them */
		if (nr_in_build_table == 2) {
			cullbuild[2] = cullbuild[1];
			cullbuild[1] = object;
			nr_in_build_table++;
			return;
		}

		/* insert somewhere in between front and back elements
		 * of a three-plus object list
		 * - oldest_build == #objects_currently_in_list
		 */
		y = 1;
		o = nr_in_build_table - 1;

		do {
			m = (y + o) / 2;

			if (object->atime > cullbuild[m]->atime)
				o = m;
			else
				y = m + 1;

		} while (y < o);

		memmove(&cullbuild[y + 1],
			&cullbuild[y],
			(nr_in_build_table - y) * sizeof(cullbuild[0]));

		cullbuild[y] = object;
		nr_in_build_table++;
		return;
	}

	/* if table is full then insert only if older than newest */
	if (nr_in_build_table > culltable_size)
		error("Cull table overfull");

	if (object->atime >= cullbuild[0]->atime)
		return;

	/* newest object in table will be displaced by this one */
	put_object(cullbuild[0]);
	cullbuild[0] = (void *)(0x6b000000 | __LINE__);
	object->usage++;

	/* place directly in first slot if second is older */
	if (object->atime >= cullbuild[1]->atime) {
		cullbuild[0] = object;
		return;
	}

	/* shift everything up one if older than oldest */
	if (object->atime <= cullbuild[culltable_size - 1]->atime) {
		memmove(&cullbuild[0],
			&cullbuild[1],
			(culltable_size - 1) * sizeof(cullbuild[0]));

		cullbuild[culltable_size - 1] = object;
		return;
	}

	/* search the table to find the insertion point
	 * - it will be between the first and last the slots
	 * - we know second is younger
	 */
	cullbuild[0] = cullbuild[1];

	y = 2;
	o = culltable_size - 1;

	do {
		m = (y + o) / 2;

		if (object->atime >= cullbuild[m]->atime)
			o = m;
		else
			y = m + 1;

	} while (y < o);

	if (y == 2) {
		cullbuild[1] = object;
		return;
	}

	memmove(&cullbuild[1],
		&cullbuild[2],
		(y - 2) * sizeof(cullbuild[0]));

	cullbuild[y - 1] = object;
}

/*****************************************************************************/
/*
 * Begin a scan to build a cull table.
 */
static void begin_building_cull_table(void)
{
	debug(1, "Refilling cull table");
	root.usage++;
	scan_cursor = &root;
}

/*****************************************************************************/
/*
 * Do the next step in building up the cull table.  Returns false upon
 * completion of a scan.
 */
static bool build_cull_table(void)
{
	struct dirent dirent, *de;
	struct object *curr, *child;
	struct stat64 st;
	unsigned loop;
	int fd;

	curr = scan_cursor;

	if (!curr->dir) {
		curr->empty = true;

		fd = openat(dirfd(curr->parent->dir), curr->name, O_DIRECTORY);
		if (fd < 0) {
			if (errno != ENOENT)
				oserror("Failed to open directory");
			goto dir_read_complete;
		}

		curr->dir = fdopendir(fd);
		if (!curr->dir)
			oserror("Failed to open directory");

		nopendir++;
	}

	debug(2, "--> build_cull_table({%s})", curr->name);

	if (fchdir(dirfd(curr->dir)) < 0)
		oserror("Failed to change current directory");

next:
	/* read the next directory entry */
	if (readdir_r(curr->dir, &dirent, &de) < 0) {
		if (errno == ENOENT)
			goto dir_read_complete;
		oserror("Unable to read directory");
	}

	if (de == NULL)
		goto dir_read_complete;

	if (dirent.d_name[0] == '.') {
		if (!dirent.d_name[1] ||
		    (dirent.d_name[1] == '.' && !dirent.d_name[2]))
			goto next;
	}

	debug(2, "readdir '%s'", dirent.d_name);

	switch (dirent.d_type) {
	case DT_UNKNOWN:
	case DT_DIR:
	case DT_REG:
		break;
	default:
		oserror("readdir returned unsupported type %d", dirent.d_type);
	}

	/* delete any funny looking files */
	if (memchr("IDSJET+@", dirent.d_name[0], 8) == NULL)
		goto found_unexpected_object;

	/* see if this object is already known to us */
	if (fstatat64(dirfd(curr->dir), dirent.d_name, &st, 0) < 0) {
		if (errno == ENOENT)
			goto next;
		oserror("Failed to stat directory");
	}

	if (!S_ISDIR(st.st_mode) &&
	    (!S_ISREG(st.st_mode) ||
	     dirent.d_name[0] == 'I' ||
	     dirent.d_name[0] == 'J' ||
	     dirent.d_name[0] == '@' ||
	     dirent.d_name[0] == '+'))
		goto found_unexpected_object;

	/* create a representation for this object */
	child = create_object(curr, dirent.d_name, &st);
	if (!child && errno == ENOENT)
		goto next;

	curr->empty = false;

	if (!child)
		oserror("Unable to create object");

	/* we consider culling objects at the transition from index object to
	 * non-index object */
	switch (child->type) {
	case OBJTYPE_DATA:
	case OBJTYPE_SPECIAL:
		if (!child->new) {
			/* the child appears to have been retained in the
			 * culling table already, so we see if it should be
			 * removed therefrom
			 */
			debug(2, "- old child");

			if (st.st_atime <= child->atime) {
				/* file on disk hasn't been touched */
				put_object(child);
				goto next;
			}

			for (loop = 0; loop < nr_in_ready_table; loop++)
				if (cullready[loop] == child)
					break;

			if (loop == nr_in_ready_table - 1) {
				/* child was oldest object */
				cullready[--nr_in_ready_table] = (void *)(0x6b000000 | __LINE__);
				put_object(child);
				goto removed;
			}
			else if (loop < nr_in_ready_table - 1) {
				/* child was somewhere in between */
				memmove(&cullready[loop],
					&cullready[loop + 1],
					(nr_in_ready_table - (loop + 1)) * sizeof(cullready[0]));
				cullready[--nr_in_ready_table] = (void *)(0x6b000000 | __LINE__);
				put_object(child);
				goto removed;
			}

			for (loop = 0; loop < nr_in_build_table; loop++)
				if (cullbuild[loop] == child)
					break;

			if (loop == nr_in_build_table - 1) {
				/* child was oldest object */
				cullbuild[--nr_in_build_table] = (void *)(0x6b000000 | __LINE__);
				put_object(child);
			}
			else if (loop < nr_in_build_table - 1) {
				/* child was somewhere in between */
				memmove(&cullbuild[loop],
					&cullbuild[loop + 1],
					(nr_in_build_table - (loop + 1)) * sizeof(cullbuild[0]));
				cullbuild[--nr_in_build_table] = (void *)(0x6b000000 | __LINE__);
				put_object(child);
			}

		removed:
			;
		}

		/* add objects that aren't in use to the cull table */
		if (!is_object_in_use(dirent.d_name)) {
			debug(2, "- insert");
			child->new = false;
			insert_into_cull_table(child);
		}
		put_object(child);
		goto next;

		/* investigate all index and index-intermediate directories */
	case OBJTYPE_INDEX:
	case OBJTYPE_INTERMEDIATE:
		debug(2, "- descend");

		child->new = false;
		scan_cursor = child;

		debug(2, "<-- build_cull_table({%s})", curr->name);
		return true;

	default:
		error("Unexpected type");
	}

	/* we've finished reading a directory - see if we can cull it */
dir_read_complete:
	debug(2, "dir_read_complete: u=%d e=%d %s",
	      curr->usage, curr->empty, curr->name);

	if (curr->dir) {
		if (curr != &root) {
			closedir(curr->dir);
			curr->dir = NULL;
			nopendir--;
		}
		else {
			rewinddir(curr->dir);
		}
	}

	if (curr->usage == 1 && curr->empty) {
		/* attempt to cull unpinned empty intermediate and index
		 * objects */
		if (fchdir(dirfd(curr->parent->dir)) < 0)
			oserror("Failed to change current directory");

		switch (curr->type) {
		case OBJTYPE_INDEX:
			cull_file(curr->name);
			break;

		case OBJTYPE_INTERMEDIATE:
			unlinkat(dirfd(curr->parent->dir), curr->name,
				 AT_REMOVEDIR);
			break;

		default:
			break;
		}
	}

	scan_cursor = curr->parent;
	if (!scan_cursor)
		debug(1, "Scan complete");

	debug(2, "<-- build_cull_table({%s})", curr->name);
	put_object(curr);
	return scan_cursor != NULL;

	/* delete unexpected objects that we've found */
found_unexpected_object:
	debug(2, "found_unexpected_object");

	destroy_unexpected_object(curr, &dirent);
	goto next;
}

/*****************************************************************************/
/*
 * decant cull entries from the build table to the ready table and enable them
 */
static void decant_cull_table(void)
{
	unsigned loop, avail, copy, leave, space, n;

	if (scan_cursor)
		error("Can't decant cull table whilst scanning");

	/* mark the new entries cullable */
	for (loop = 0; loop < nr_in_build_table; loop++) {
		if (!cullbuild[loop]->cullable) {
			cullbuild[loop]->cullable = true;
			ncullable++;
		}
	}

	/* if the ready table is empty, copy the whole lot across */
	if (nr_in_ready_table == 0) {
		copy = nr_in_build_table;

		debug(1, "Decant (all %d)", copy);

		n = copy * sizeof(cullready[0]);
		memcpy(cullready, cullbuild, n);
		memset(cullbuild, 0x6e, n);
		nr_in_ready_table = nr_in_build_table;
		nr_in_build_table = 0;
		goto check;
	}

	/* decant some of the build table if there's space */
	if (culltable_size < nr_in_ready_table)
		error("Less than zero space in ready table");
	space = culltable_size - nr_in_ready_table;
	if (space == 0)
		goto check;

	/* work out how much of the build table we can copy */
	copy = avail = nr_in_build_table;
	if (copy > space)
		copy = space;
	leave = avail - copy;

	debug(1, "Decant (%u/%u to %u)", copy, avail, space);

	/* make a hole in the ready table transfer "copy" elements from the end
	 * of cullbuild (oldest) to the beginning of cullready (youngest)
	 */
	memmove(&cullready[copy], &cullready[0], nr_in_ready_table * sizeof(cullready[0]));
	nr_in_ready_table += copy;

	memcpy(&cullready[0], &cullbuild[leave], copy * sizeof(cullready[0]));
	memset(&cullbuild[leave], 0x6b, copy * sizeof(cullbuild[0]));
	nr_in_build_table = leave;

	if (copy + leave > culltable_size)
		error("Scan table exceeded (%d+%d)", copy, leave);

check:
	for (loop = 0; loop < nr_in_ready_table; loop++)
		if (((long)cullready[loop] & 0xf0000000) == 0x60000000)
			abort();
}

/*****************************************************************************/
/*
 * get the directory handle for the given directory
 */
static int get_dir_fd(struct object *dir)
{
	int parentfd, fd;

	debug(1, "get_dir_fd(%s)", dir->name);

	if (dir->dir) {
		fd = dup(dirfd(dir->dir));
		if (fd < 0)
			oserror("Failed to dup fd");
		debug(1, "cache fd to %d", fd);
		return fd;
	}

	parentfd = get_dir_fd(dir->parent);

	fd = openat(parentfd, dir->name, O_DIRECTORY);
	if (fd < 0 && errno != ENOENT)
		oserror("Failed to open directory");

	/* return parent fd or -1 if ENOENT */
	debug(1, "<%d>/%s to %d", parentfd, dir->name, fd);
	close(parentfd);
	return fd;
}

/*****************************************************************************/
/*
 * cull an object
 */
static void cull_object(struct object *object)
{
	struct stat64 st;
	int dirfd;

	debug(1, "CULL %s", object->name);

	dirfd = get_dir_fd(object->parent);
	if (dirfd >= 0) {
		if (fstatat64(dirfd, object->name, &st, 0) < 0) {
			if (errno != ENOENT)
				oserror("Failed to re-stat object");

			close(dirfd);
			goto object_already_gone;
		}

		if (fchdir(dirfd) < 0)
			oserror("Failed to change current directory");
		if (object->atime >= st.st_atime)
			cull_file(object->name);

		close(dirfd);
	}

object_already_gone:
	put_object(object);
}

/*****************************************************************************/
/*
 * consider starting a cull
 */
static void cull_objects(void)
{
	if (ncullable <= 0)
		error("Cullable object count is inconsistent");

	if (cullready[nr_in_ready_table - 1]->cullable) {
		cull_object(cullready[nr_in_ready_table - 1]);
		cullready[--nr_in_ready_table] = (void *)(0x6b000000 | __LINE__);
	}
}
