/*-------------------------------------------------------------------------
This is an AWS-ARG-ATS-Science intern project developed by the intern
Joseph Reeves (jsreeves@) and mentor Benjamin Kiesl-Reiter (benkiesl@).

This code extends the solver yal-lin (Md Solimul Chowdhury, Cayden Codel, Marijn Heule), found at the [Github repository](https://github.com/solimul/yal-lin), which itself extended the solver [yalsat](https://github.com/arminbiere/yalsat) (Armin Biere).
-------------------------------------------------------------------------*/

/*

  Main driver for the solver.

  Functionality:
  - parse input options
  - parse input formula
    - accepted formats: CNF, KNF (weighted WCNF/WKNF are rejected)
  - call solver (yals.c)
  - write solution to "witness.sol"

  Lingering support for parallel solving (palsat) has not been updated
  for CaLFwSAT. 

  Can modify code to write solution to stdout.
    - look at "if (0) { // writing solution to standard out instead of a file"

*/

#include "yals.h"

/*------------------------------------------------------------------------*/

#define YALSINTERNAL
#include "yils_card.h"

/*------------------------------------------------------------------------*/

#include <assert.h>
#include <ctype.h>
#include <limits.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>
#include <stdarg.h>
#include <math.h>

/*------------------------------------------------------------------------*/
#ifdef PALSAT
#include <pthread.h>
#include <sys/time.h>
#endif
/*------------------------------------------------------------------------*/

#ifdef PALSAT
#define THREADS 12
typedef struct Worker { Yals * yals; pthread_t thread; } Worker;
static Worker * worker;
static YalsProbePool * probe_pool;       // shared across all palsat workers
static int done, winner, threads = THREADS, threadset;
struct { pthread_mutex_t done, msg, mem; } lock;
#else
static Yals * yals;
static YalsProbePool * probe_pool;       // single-solver case: still useful for bypass-against-self
static int flipsset, memsset;
static long long flips = -1, mems = -1;
#endif
static unsigned long long seed;
static int seedset, closefile, verbose;
static const char * filename;
static FILE * file;
static int V, C;

struct { size_t allocated, max; } mem;

/*------------------------------------------------------------------------*/
#ifndef NDEBUG
static int logging, checking;
#endif
/*------------------------------------------------------------------------*/

#ifdef PALSAT
#define YALS worker[0].yals
#define WINNER worker[winner].yals
#define NAME "PalSAT"
#else
#define YALS yals
#define WINNER yals
#define NAME "CaLFwSAT"
#endif

static double average (double a, double b) { return b ? a/b : 0; }

/*------------------------------------------------------------------------*/

#ifdef PALSAT
#define LOCK(MUTEX) \
do { \
  if (pthread_mutex_lock (&lock.MUTEX)) \
    msg ("failed to lock '%s' mutex in '%s'", #MUTEX, __FUNCTION__); \
} while (0)
#define UNLOCK(MUTEX) \
do { \
  if (pthread_mutex_unlock (&lock.MUTEX)) \
    msg ("failed to unlock '%s' mutex in '%s'", #MUTEX, __FUNCTION__); \
} while (0)
#else
#define LOCK(MUTEX) do { } while (0)
#define UNLOCK(MUTEX) do { } while (0)
#endif

/*------------------------------------------------------------------------*/

static void die (const char * fmt, ...) {
  va_list ap;
#ifdef PALSAT
  pthread_mutex_lock (&lock.msg);
#endif
  fflush (stdout);
  printf ("*** error: ");
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
#ifdef PALSAT
  pthread_mutex_unlock (&lock.msg);
#endif
  exit (1);
}

static void perr (const char * fmt, ...) {
  va_list ap;
#ifdef PALSAT
  pthread_mutex_lock (&lock.msg);
#endif
  fflush (stdout);
  printf ("*** parse error: ");
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
#ifdef PALSAT
  pthread_mutex_unlock (&lock.msg);
#endif
  exit (1);
}

static void msg (const char * fmt, ...) {
  va_list ap;
#ifdef PALSAT
  pthread_mutex_lock (&lock.msg);
#endif
  fflush (stdout);
  fputs ("c ", stdout);
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
#ifdef PALSAT
  pthread_mutex_unlock (&lock.msg);
#endif
}

/*------------------------------------------------------------------------*/
#ifdef PALSAT

static double start;

static double currentime () {
  double res = 0;
  struct timeval tv;
  if (!gettimeofday (&tv, 0))
    res = 1e-6 * tv.tv_usec, res += tv.tv_sec;
  return res;
}

static double getime () { return currentime () - start; }

#else

static double getime () { return yals_process_time (); }

#endif
/*------------------------------------------------------------------------*/

#define INCB(BYTES) \
do { \
  LOCK (mem); \
  mem.allocated += (BYTES); \
  if (mem.allocated > mem.max) mem.max = mem.allocated; \
  UNLOCK (mem); \
} while (0)

#define DEC(BYTES) \
do { \
  LOCK (mem); \
  assert (mem.allocated >= (BYTES)); \
  mem.allocated -= (BYTES); \
  UNLOCK (mem); \
} while (0)

static void * mymalloc (void * dummy, size_t bytes) {
  void * res = malloc (bytes);
  if (!res) die ("out of memory during 'malloc'");
  (void) dummy;
  INCB (bytes);
  return res;
}

static void myfree (void * dummy, void * ptr, size_t bytes) {
  DEC (bytes);
  free (ptr);
}

static void * myrealloc (void * dummy, void * ptr, size_t o, size_t n) {
  void * res;
  DEC (o);
  res = realloc (ptr, n);
  if (!res) die ("out of memory during 'realloc'");
  INCB (n);
  return res;
}

/*------------------------------------------------------------------------*/

static int hasuffix (const char * arg, const char * suffix) {
  if (strlen  (arg) < strlen (suffix)) return 0;
  if (strcmp (arg + strlen (arg) - strlen (suffix), suffix)) return 0;
  return 1;
}

static int cmd (const char * arg, const char * suffix, const char * fmt) {
  struct stat buf;
  char * cmd;
  int len;
  if (!hasuffix (arg, suffix)) return 0;
  if (stat (arg, &buf)) die ("can not stat file '%s'", arg);
  len = strlen (fmt) + strlen (arg) + 1;
  cmd = mymalloc (YALS, len);
  sprintf (cmd, fmt, arg);
  file = popen (cmd, "r");
  myfree (YALS, cmd, len);
  closefile = 2;
  filename= arg;
  return 1;
}

static unsigned long long atoull (const char * str) {
  unsigned long long res = 0;
  const char * p = str;
  int ch;
  while (isdigit (ch = *p++))
    res = 10ull * res + (ch - '0');
  return res;
}

/*------------------------------------------------------------------------*/

static char valine[76];
static int nvaline;

static void printvaline () {
  fputc ('v', stdout);
  assert (nvaline < sizeof valine);
  fputs (valine, stdout);
  fputc ('\n', stdout);
  nvaline = 0;
}

static void writevaline (FILE *file) {
  fputc ('v', file);
  assert (nvaline < sizeof valine);
  fputs (valine, file);
  fputc ('\n', file);
  nvaline = 0;
}

static void printval (int lit) {
  char buffer[12];
  int len;
  sprintf (buffer, " %d", lit);
  len = strlen (buffer);
  if (nvaline + len + 1 >= sizeof valine) printvaline ();
  strcpy (valine + nvaline, buffer);
  nvaline += len;
  assert (nvaline < sizeof valine);
}

static void writeval (FILE* file, int lit) {
  char buffer[12];
  int len;
  sprintf (buffer, " %d", lit);
  len = strlen (buffer);
  if (nvaline + len + 1 >= sizeof valine) writevaline (file);
  strcpy (valine + nvaline, buffer);
  nvaline += len;
  assert (nvaline < sizeof valine);
}

/*------------------------------------------------------------------------*/

static void stats () {
#ifdef PALSAT
  double t, w;
  int i;
  for (i = 0; i < threads; i++) {
    Yals * y = worker[i].yals;
    msg ("");
    yals_msg (y, 0, "final worker %d minimum of %d unsatisfied clauses",
      i, yals_minimum (y));
    if (verbose) yals_stats (y);
  }
  // Combined per-probe best-score histogram + global --bypass stats
  // + --heat per-variable counters (if enabled).
  if (verbose) {
    Yals ** ys = malloc ((size_t) threads * sizeof (Yals *));
    for (i = 0; i < threads; i++) ys[i] = worker[i].yals;
    msg ("");
    yals_print_combined_bypass_stats (ys, threads);
    yals_print_combined_probe_hist (ys, threads);
    yals_print_combined_heat (ys, threads);
    // Heat-slack ranking (lowest 20 constraints by heat-implied slack).
    yals_print_heat_slack (WINNER, 20);
    free (ys);
  }
  msg ("");
  w = getime ();
  t = yals_process_time ();
  msg ("total wall clock time of %.2f seconds", w);
  msg ("total process time of %.2f seconds", t);
  msg ("utilization %.1f%% for %d threads",
    (w ? 100.0*t/w/(double)threads : 0), threads);
  {
    long long total_flips = 0;
    for (i = 0; i < threads; i++) total_flips += yals_flips (worker[i].yals);
    msg ("total flips %lld", total_flips);
  }
  msg ("");
  yals_print_length_weights (WINNER);
#else
  msg ("");
  msg ("final minimum of %d unsatisfied hard constraints", yals_minimum (yals));
  if (verbose) yals_stats (yals);
  // Per-probe best-score histogram + global --bypass stats + --heat
  // (single solver). Same call shape as palsat for consistency.
  if (verbose) {
    Yals * single[1] = { yals };
    yals_print_combined_bypass_stats (single, 1);
    yals_print_combined_probe_hist (single, 1);
    yals_print_combined_heat (single, 1);
    yals_print_heat_slack (yals, 20);
  }
  msg ("total flips %lld", yals_flips (yals));
  yals_print_length_weights (yals);
  msg ("total process time of %.2f seconds", getime ());
  printf ("%f %.1f |\n", yals_process_time (), mem.max/(double)(1<<20) );
#endif
  msg ("maximally allocated %.1f MB", mem.max/(double)(1<<20));
}

static void write_witness () {
  int i, lit;
  FILE *file;
  file = fopen ("witness.sol", "w+");
  for (i = 1; i <= V; i++) {
  lit = (yals_deref (WINNER, i) > 0) ? i : -i;
    writeval (file,lit);
  }
    writeval (file,0);
  if (nvaline) {
      writevaline (file);
  }
  fclose (file);
}

static void (*sig_int_handler)(int);
static void (*sig_segv_handler)(int);
static void (*sig_abrt_handler)(int);
static void (*sig_term_handler)(int);

static void resetsighandlers (void) {
  (void) signal (SIGINT, sig_int_handler);
  (void) signal (SIGSEGV, sig_segv_handler);
  (void) signal (SIGABRT, sig_abrt_handler);
  (void) signal (SIGTERM, sig_term_handler);
}

static int catchedsig;

// Set by catchsig() on SIGINT/SIGTERM. Read by the worker termination
// callbacks (terminate / terminate_single). volatile sig_atomic_t is the only
// thing a signal handler may safely touch here.
static volatile sig_atomic_t terminating;

static void catchsig (int sig) {
  if (sig == SIGINT || sig == SIGTERM) {
    if (!terminating) {
      // Async-signal-safe path: only raise a flag and write() a short notice.
      // The per-worker term callback sees the flag and unwinds every worker;
      // the main thread then prints stats/witness *after* join, on a normal
      // (non-handler) stack. This replaces the old async-UNSAFE handler, which
      // called stats()/printf/write_witness()/malloc directly and could
      // deadlock on a stdio or heap lock -> the "CAUGHT SIGNAL but still
      // running" hang.
      static const char m[] =
        "c\nc [CaLFwSAT] CAUGHT SIGNAL, terminating workers"
        " (signal again to force)...\nc\n";
      ssize_t n = write (1, m, sizeof m - 1);
      (void) n;
      terminating = 1;
      return;
    }
    // Second interrupt: stop waiting for a clean unwind and die now.
    resetsighandlers ();
    raise (sig);
    return;
  }
  // SIGSEGV / SIGABRT: a crash, no clean unwind is possible. Emit a marker
  // (async-safe) and re-raise with the default handler.
  if (!catchedsig) {
    static const char m[] = "c s UNKNOWN\n";
    ssize_t n = write (1, m, sizeof m - 1);
    (void) n;
    catchedsig = 1;
  }
  resetsighandlers ();
  raise (sig);
}

static void setsighandlers (void) {
  sig_int_handler = signal (SIGINT, catchsig);
  sig_segv_handler = signal (SIGSEGV, catchsig);
  sig_abrt_handler = signal (SIGABRT, catchsig);
  sig_term_handler = signal (SIGTERM, catchsig);
}

#ifndef PALSAT
// Single-instance counterpart of terminate(): lets the lone worker unwind on
// SIGINT/SIGTERM so the normal exit path prints stats/witness after it returns.
static int terminate_single (void * dummy) {
  (void) dummy;
  return terminating;
}
#endif

/*------------------------------------------------------------------------*/

static int isnum (const char * p) {
  int ch;
  if ((ch = *p) == '-') ch = *++p;
  if (!isdigit (ch)) return 0;
  while (isdigit (ch = *++p))
    ;
  return !ch;
}

static int isfile (const char * p) {
  struct stat buf;
  return !stat (p, &buf);
}

static int setopt (const char * name, int val) {
  int res;
#ifdef PALSAT
  int i;
  res = 0;
  for (i = 0; i < threads; i++)
    res = yals_setopt (worker[i].yals, name, val);
#else
  res = yals_setopt (yals, name, val);
#endif
  return res;
}

// Normalize an option name: convert dashes to underscores in-place so the
// user can write either --min-weight or --min_weight; both look up the same
// internal identifier. Stops at the first '=' or end of string.
static void normalize_opt_name (char * name) {
  for (char * p = name; *p && *p != '='; p++)
    if (*p == '-') *p = '_';
}

static int opt (const char * arg) {
  int res = 0;
  assert (arg[0] == '-');
  if (arg[1] == '-') {
    if (arg[2] == 'n' && arg[3] == 'o' && arg[4] == '-') {
      // --no-<name>: name follows; normalize it too.
      int sublen = strlen (arg + 5) + 1;
      char * name = mymalloc (0, sublen);
      strcpy (name, arg + 5);
      normalize_opt_name (name);
      res = setopt (name, 0);
      myfree (0, name, sublen);
    }
    else {
      int len = strlen (arg);
      char * name = mymalloc (0, len - 1), * val;
      strcpy (name, arg + 2);
      normalize_opt_name (name);
      for (val = name; *val && *val != '='; val++)
	;
      if (!*val) res = setopt (name, 1);
      else if (*val == '=') {
	*val++ = 0;
	if (isnum (val))
	  res = setopt (name, atoi (val));
      }
      myfree (0, name, len - 1);
    }
  }
  return res;
}

/*------------------------------------------------------------------------*/
#ifdef PALSAT

static void lockmsg (void* dummy) {
  (void) dummy;
  pthread_mutex_lock (&lock.msg);
}

static void unlockmsg (void* dummy) {
  (void) dummy;
  pthread_mutex_unlock (&lock.msg);
}

static int setdone (int w, int r) {
  int res;
  LOCK (done);
  if (r) { winner = w; done = r; }
  res = winner;
  UNLOCK (done);
  return res;
}

static int terminate (void * dummy) {
  int res;
  (void) dummy;
  if (terminating) return 1;   // SIGINT/SIGTERM: unwind this worker
  LOCK (done);
  res = done;
  UNLOCK (done);
  return res;
}

static void * run (void * p) {
  Worker * w = p;
  int res, widx = w - worker;
  assert (0 <= widx), assert (widx < threads);
  yals_set_wid (w->yals, widx);
  res = yals_sat (w->yals);
  if (res && setdone (widx, res) == widx)
    msg ("worker %d wins with result %d", widx, res);
  else msg ("worker %d returns with %d", widx, res);
  return p;
}

static int palsat () {
  int i;
  for (i = 0; i < threads; i++)
    if (pthread_create (&worker[i].thread, 0, run, worker + i))
      die ("failed to created thread %d", i);
    else msg ("created thread %d", i);
  for (i = 0; i < threads; i++)
    if (pthread_join (worker[i].thread, 0))
      die ("failed to join thread %d", i);
    else msg ("joined thread %d", i);
  msg ("");
  return done;

}

#endif
/*------------------------------------------------------------------------*/

#ifdef PALSAT
static void initlocks () {
  pthread_mutex_init (&lock.mem, 0);
  pthread_mutex_init (&lock.msg, 0);
  pthread_mutex_init (&lock.done, 0);
}

static int getsystemcores (int explain) {
  int syscores, coreids, physids, procpuinfocores;
  int usesyscores, useprocpuinfo, amd, intel, res;
  FILE * p;

  syscores = sysconf (_SC_NPROCESSORS_ONLN);
  if (explain) {
    if (syscores > 0)
      msg ("'sysconf' reports %d processors online", syscores);
    else
      msg ("'sysconf' fails to determine number of online processors");
  }

  p = popen ("grep '^core id' /proc/cpuinfo 2>/dev/null|sort|uniq|wc -l", "r");
  if (p) {
    if (fscanf (p, "%d", &coreids) != 1) coreids = 0;
    if (explain) {
      if (coreids > 0) 
	msg ("found %d unique core ids in '/proc/cpuinfo'", coreids);
      else
	msg ("failed to extract core ids from '/proc/cpuinfo'");
    }
    pclose (p);
  } else coreids = 0;

  p = popen (
        "grep '^physical id' /proc/cpuinfo 2>/dev/null|sort|uniq|wc -l", "r");
  if (p) {
    if (fscanf (p, "%d", &physids) != 1) physids = 0;
    if (explain) {
      if (physids > 0) 
	msg ("found %d unique physical ids in '/proc/cpuinfo'", 
            physids);
      else
	msg ("failed to extract physical ids from '/proc/cpuinfo'");
    }
    pclose (p);
  } else physids = 0;

  if (coreids > 0 && physids > 0 && 
      (procpuinfocores = coreids * physids) > 0) {
    if (explain)
      msg ("%d cores = %d core times %d physical ids in '/proc/cpuinfo'",
           procpuinfocores, coreids, physids);
  } else procpuinfocores = 0;

  usesyscores = useprocpuinfo = 0;

  if (procpuinfocores > 0 && procpuinfocores == syscores) {
    if (explain) msg ("'sysconf' and '/proc/cpuinfo' results match");
    usesyscores = 1;
  } else if (procpuinfocores > 0 && syscores <= 0) {
    if (explain) msg ("only '/proc/cpuinfo' result valid");
    useprocpuinfo = 1;
  } else if (procpuinfocores <= 0 && syscores > 0) {
    if (explain) msg ("only 'sysconf' result valid");
    usesyscores = 1;
  } else {
    intel = !system ("grep vendor /proc/cpuinfo 2>/dev/null|grep -q Intel");
    if (intel && explain) 
      msg ("found Intel as vendor in '/proc/cpuinfo'");
    amd = !system ("grep vendor /proc/cpuinfo 2>/dev/null|grep -q AMD");
    if (amd && explain) 
      msg ("found AMD as vendor in '/proc/cpuinfo'");
    assert (syscores > 0);
    assert (procpuinfocores > 0);
    assert (syscores != procpuinfocores);
    if (amd) {
      if (explain) msg ("trusting 'sysconf' on AMD");
      usesyscores = 1;
    } else if (intel) {
      if (explain) {
	msg (
	     "'sysconf' result off by a factor of %f on Intel", 
	     syscores / (double) procpuinfocores);
	msg ("trusting '/proc/cpuinfo' on Intel");
      }
      useprocpuinfo = 1;
    }  else {
      if (explain)
	msg ("trusting 'sysconf' on unknown vendor machine");
      usesyscores = 1;
    }
  } 
  
  if (useprocpuinfo) {
    if (explain) 
      msg (
        "assuming cores = core * physical ids in '/proc/cpuinfo' = %d",
        procpuinfocores);
    res = procpuinfocores;
  } else if (usesyscores) {
    if (explain) 
      msg ("assuming cores = number of processors reported by 'sysconf' = %d",
           syscores);
    res = syscores;
  } else {
    if (explain) 
      msg ("using compiled in default value of %d workers", THREADS);
    res = THREADS;
  }

  return res;
}
#endif

static void usage () {
#ifdef PALSAT
  printf (
    "usage: palsat [<option> ...] [<file> [<seed>]]\n");
#else
  printf (
    "usage: CaLFwSAT -v --cutoff=<#flips> --maxtries=<#restarts> [--option=<val>] <Formula> [seed]\n");
#endif
  printf ("\n");
  printf ("main options: \n");
  printf ("\n");
  printf ("-h          print this command line option summary\n");
  printf ("--version   version number and exit\n");
  printf ("\n");
#ifdef PALSAT
  printf ("-t <num>  number of worker threads (system default %d)\n",
    getsystemcores (0));
  printf ("\n");
#endif
  printf ("-v     increase verbose level (see '--verbose')\n");
  printf ("-n     do not print witness (see '--witness')\n");
#ifndef NDEBUG
  printf ("-l     enable internal logging (see '--logging')\n");
  printf ("-c     enable internal checking (see '--checking')\n");
#endif
  printf ("\n");
  printf ("other options (also available through API): \n");
  printf ("\n");
  {
    Yals * y = yals_new_with_mem_mgr (0, mymalloc, myrealloc, myfree);
    yals_usage (y);
    yals_del (y);
  }
  printf ("\n");
  printf ("The long options are by default used as '--<name>=<val>'.\n");
  printf ("Alternatively '--<name>' is the same as '--<name>=1' and\n");
  printf ("further '--no-<name>' is the same as '--<name>=0'.\n");
}

static void version () { printf ("%s\n", yals_version ()); }

int main (int argc, char** argv) {
  int i, ch, sign, lit, res, m, n;
  int cardinality, bound;
  int is_weighted = 0;
  double max_weight = 0;
#ifdef PALSAT
  // When set, the formula is parsed into worker 0 only and shared (read-only)
  // with the other workers, instead of giving each worker its own copy. Decided
  // once the header is parsed (see below).
  int share_formula = 0;
#endif

#ifdef PALSAT
  // Initialize mutexes before any option handling: '-h'/usage() allocates via
  // mymalloc, which locks the 'mem' mutex.
  initlocks ();
#endif

  for (i = 1; i < argc; i++) {
#ifdef PALSAT
    if (!strcmp (argv[i], "-t")) { i++; continue; }
#endif
    if (!strcmp (argv[i], "-v")) { verbose++; continue; }
    if (!strcmp (argv[i], "--version")) { version (); exit (0); }
    if (!strcmp (argv[i], "-h")) { usage (); exit (0); }
  }
#ifdef PALSAT
  printf ("c PalSAT Yet Another Local Search Solver\n");
  printf ("c Parallel Simple Portfolio Version\n");
#else
  printf ("c CaLFwSAT local search solver\n");
#endif
  yals_banner ("c ");
#ifdef PALSAT
  for (i = 1; i < argc; i++) {
    if (strcmp (argv[i], "-t")) continue;
    if (++i == argc) die ("argument to '-t' missing (try '-h')");
    if (threadset)
      die ("multiple '-t' options: '-t %d' and '-t %s' (try '-h')",
        threads, argv[i]);
    if ((threads = atoi (argv[i])) < 1)
      die ("invalid argument in '-t %s' (try '-h')", argv[i]);
    threadset = 1;
  }
  start = currentime ();
  if (threadset)
    msg ("using %d solver instances and %d worker threads ('-t %d')",
      threads, threads, threads);
  else  {
    threads = getsystemcores (1);
    msg ("using %d solver instances and %d worker threads (default)",
      threads, threads);
  }
  msg ("creating %d solver instances", threads);
  worker = mymalloc (0, threads * sizeof *worker);
  for (i = 0; i < threads; i++) {
    char prefix[80];
    Yals * y = yals_new_with_mem_mgr (0, mymalloc, myrealloc, myfree);
    yals_setmsglock (y, lockmsg, unlockmsg, 0);
    yals_seterm (y, terminate, 0);
    sprintf (prefix, "c %02d ", i);
    yals_setprefix (y, prefix);
    yals_setime (y, getime);
    worker[i].yals = y;
  }
#else
  yals = yals_new_with_mem_mgr (0, mymalloc, myrealloc, myfree);
  yals_setprefix (yals, "c ");
  yals_seterm (yals, terminate_single, 0);
  // Shared probe-best pool (in this build, "shared" = "self"): same
  // bypass mechanism works with a single solver, accumulating against
  // its own history.
  probe_pool = yals_probe_pool_new ();
  yals_set_probe_pool (yals, probe_pool);
#endif
  verbose = 0;
  for (i = 1; i < argc; i++) {
#ifdef PALSAT
    if (!strcmp (argv[i], "-t")) { i++; assert (i < argc); continue; }
#endif
    if (!strcmp (argv[i], "-v"))
      setopt ("verbose", ++verbose);
    else if (!strcmp (argv[i], "-n"))
      setopt ("witness", 0);
#ifndef NDEBUG
    else if (!strcmp (argv[i], "-l"))
      setopt ("logging", ++logging);
    else if (!strcmp (argv[i], "-c"))
      setopt ("checking", ++checking);
#endif
    else if (isnum (argv[i])) {
#ifdef PALSAT
      if (seedset) die ("seed already set (try '-h')");
#else
      if (memsset) die ("more than three numbers (try '-h')");
      else if (flipsset) mems = atoll (argv[i]), memsset = 1;
      else if (seedset) flips = atoll (argv[i]), flipsset = 1;
#endif
      else seed = atoull (argv[i]), seedset = 1;
    }  
    
    else if (!strcmp (argv[i], "--clsselectp")) setopt ("clsselectp", atoll (argv[++i]));
    else if (!strcmp (argv[i], "--slope")) setopt ("slope", atoll (argv[++i]));
    else if (!strcmp (argv[i], "--floor")) setopt ("floor", atoll (argv[++i]));
    else if (!strcmp (argv[i], "--wtpow")) setopt ("wtpow", atoll (argv[++i]));
    else if (!strcmp (argv[i], "--maxtries")) { setopt ("maxtries", atoll (argv[++i]));}
    else if (!strcmp (argv[i], "--cutoff")) { setopt ("cutoff", atoll (argv[++i]));}

    else if (!strcmp (argv[i], "-")) {
      if (filename)
	die ("file '%s' and '-' specified (try '-h')", filename);
      file = stdin, filename = "<stdin>";
      assert (!closefile);
    } else if (argv[i][0] == '-') {
      if (!opt (argv[i]))
	die ("invalid command line option '%s'", argv[i]);
    } else if (!isfile (argv[i]))
      die ("'%s' does not seem to be a file", argv[i]);
    else if (cmd (argv[i], ".gz", "gunzip -c %s"))
      ;
    else if (cmd (argv[i], ".bz2", "bunzip -d -c %s"))
      ;
    else if (cmd (argv[i], ".xz", "xz -d -c %s"))
      ;
    else if (!(file = fopen (argv[i], "r")))
      die ("can not read '%s'", argv[i]);
    else
      closefile = 1, filename = argv[i];
  }
#ifdef PALSAT
  // Shared probe-best pool: always allocated. Tracks per-probe stats.pbest
  // across all workers; consumed by --bypass.
  probe_pool = yals_probe_pool_new ();
  for (i = 0; i < threads; i++)
    yals_set_probe_pool (worker[i].yals, probe_pool);
#endif
  setsighandlers ();
  verbose = yals_getopt (YALS, "verbose");
  if (verbose) {
#ifdef PALSAT
    Yals * y = worker[0].yals;
    yals_setprefix (y, "c ");
    yals_showopts (y);
    yals_setprefix (y, "c 00 ");
#else
    yals_showopts (yals);
#endif
  }
#ifndef NDEBUG
  logging = yals_getopt (YALS, "logging");
  checking = yals_getopt (YALS, "checking");
  if (logging && verbose < 2) setopt ("verbose", verbose = 2);
#endif
  if (seedset) {
    msg ("using specified seed %llu", seed);
    yals_srand (YALS, seed);
  } else msg ("no seed specified (using default 0)");
#ifdef PALSAT
  {
    unsigned long long newseed = seed;
    for (i = 1; i < threads; i++) {
      newseed *= 1103515245;
      newseed += 12345;
      yals_srand (worker[i].yals, newseed);
      msg ("worker %d uses seed %llu", i, newseed);
    }
  }
#else
  if (flipsset) msg ("using specified flips limit %lld", flips);
  else msg ("no flips limit set (by default)");
  if (memsset) msg ("using specified mems limit %lld", mems);
  else msg ("no mems limit set (by default)");
#endif
  if (!file) file = stdin, filename = "<stdin>";
  msg ("parsing '%s'", filename);
HEADER:
  ch = getc (file);
  if (ch == 'c') {
    while ((ch = getc (file)) != '\n')
      if (ch == EOF) perr ("end-of-file in comment");
    goto HEADER;
  }
  if (ch != 'p') perr ("expected 'p' or 'c'");
  ungetc (ch, file);
  if (fscanf (file, "p cnf %d %d", &m, &n) != 2 || m < 0 || n < 0) {
    if (fscanf (file, "knf %d %d", &m, &n) != 2 || m < 0 || n < 0) { // check for p knf header
      is_weighted = 1;
      if (fscanf (file, "wcnf %d %d %lf", &m, &n, &max_weight) != 3|| m < 0 || n < 0 || max_weight < 0) {// check for p wcnf header
        if (fscanf (file, "knf %d %d %lf", &m, &n, &max_weight) != 3 || m < 0 || n < 0 || max_weight < 0) { // check for p wknf header
          perr ("invalid header"); // p parsed in first fscanf
        }
      }
    }
  }
  if (is_weighted)
    die ("MaxSAT/weighted input no longer supported; use plain CNF/KNF");
  msg ("parsed header with ' %d %d'", m, n);

  V = m, C = n;
  msg ("clause variable ratio %.2f", average (C,V));
  lit = 0;

#ifdef PALSAT
  // Share a single read-only formula across workers when running more than one
  // worker.
  share_formula = (threads > 1);
  if (share_formula)
    msg ("parsing formula once and sharing it across %d workers", threads);
#endif

cardinality = bound = 0; // track when a cardinality constraint is parsed

BODY:
  ch = getc (file);
  if (ch == EOF) {
    if (n >= 1) perr ("one clause missing");
    if (n > 0) perr ("clauses missing");
    if (lit) perr ("zero sentinel missing at end-of-file");
    goto DONE;
  }
  if (ch == ' ' || ch == '\t' || ch == '\r' || ch == '\n') goto BODY;
  if (ch == 'k') {
    // cardinality constraint
    cardinality = 1;
    goto BODY; // next, parse the bound
  }
  if (ch == 'c') {
    while ((ch = getc (file)) != '\n')
      if (ch == EOF) perr ("end-of-file in comment");
    goto BODY;
  }
  if (ch == '-') {
    ch = getc (file);
    if (ch == '0') perr ("expected non-zero digit");
    sign = -1;
  } else sign = 1;
  if (!isdigit (ch)) perr ("expected digit");
  lit = ch - '0';
  while (isdigit (ch = getc (file)))
    lit = 10*lit + (ch - '0');
  if (ch != EOF && ch != ' ' && ch != '\r' && ch != '\n')
    perr ("expected space or new-line");
  if (lit > V) perr ("maximum variable index exceeded");
  if (!n) perr ("too many clauses");
  lit *= sign;
  if (!lit) n--;
#ifdef PALSAT
  // In shared mode parse into worker 0 only; otherwise into every worker.
  if (cardinality && !bound) {
    int i, nw = share_formula ? 1 : threads;
    for (i = 0; i < nw; i++)
      yals_card_add (worker[i].yals, lit, 1); // add bound for new cardinality constraint
    bound = 1;
    goto BODY;
  }
  {
    int i, nw = share_formula ? 1 : threads;
    if (cardinality) {
      for (i = 0; i < nw; i++)
        yals_card_add (worker[i].yals, lit, 0); // add literal to cardinality constraint
    } else {
      for (i = 0; i < nw; i++)
        yals_add (worker[i].yals, lit);
    }
  }
  if (!lit) { // finished parsing a constraint, reset flags
    cardinality = bound = 0;
  }
#else
  if (cardinality && !bound) {
    yals_card_add (yals, lit, 1); // add bound for new cardinality constraint
    bound = 1;
    goto BODY;
  }
  if (cardinality) {
    yals_card_add (yals, lit, 0); // add literal to cardinality constraint
  } else {
    yals_add (yals, lit);
  }
  if (!lit) { // finished parsing a clause, reset cardinality and bound flags
    cardinality = bound = 0;
  }
#endif
  goto BODY;
DONE:
  if (closefile == 1) fclose (file);
  if (closefile == 2) pclose (file);
  msg ("finished parsing after %.2f seconds",  getime ());
  msg ("allocated %.1f MB after parsing", mem.allocated/(double)(1<<20));
#ifdef PALSAT
  if (share_formula) {
    // Simplify the formula once on the owner, then point the other workers at it
    // so a single read-only copy is shared instead of one per worker.
    if (yals_prepare_shared_formula (worker[0].yals) == 20)
      res = 20;
    else {
      for (i = 1; i < threads; i++)
        yals_share_formula (worker[i].yals, worker[0].yals);
      msg ("allocated %.1f MB after sharing", mem.allocated/(double)(1<<20));
      res = palsat ();
    }
  } else
    res = palsat ();
#else
  if (flipsset) yals_setflipslimit (yals, flips);
  if (memsset) yals_setmemslimit (yals, mems);
  yals_set_wid (yals, -1);
  res = yals_sat (yals);
  msg ("");
#endif
  if (res != 20) {
    if (res == 10) fputs ("s SATISFIABLE\n", stdout);
    else if (yals_getopt (WINNER, "witness")) fputs ("s CURRENT BEST\n", stdout);
    else fputs ("s UNKNOWN\n", stdout);
    write_witness ();
    // Also print the satisfying assignment to stdout in DIMACS 'v' lines,
    // so palsat / CaLFwSAT can be used in pipelines without reading witness.sol.
    if (res == 10 && yals_getopt (WINNER, "witness")) {
      fflush (stdout);
      for (i = 1; i <= V; i++) {
        lit = (yals_deref (WINNER, i) > 0) ? i : -i;
        printval (lit);
      }
      printval (0);
      if (nvaline) {
        printvaline ();
      }
    }
  } else fputs ("s UNSATISFIABLE\n", stdout);
  fflush (stdout);
  resetsighandlers ();
  stats ();
#ifdef PALSAT
  for (i = 0; i < threads; i++) yals_del (worker[i].yals);
  myfree (0, worker, threads * sizeof *worker);
  yals_probe_pool_delete (probe_pool);
#else
  yals_del (yals);
  yals_probe_pool_delete (probe_pool);
#endif
  msg ("");
  msg ("%s returns with exit code %d", NAME, res);
  return res;
}
