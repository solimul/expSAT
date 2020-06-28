/***************************************************************************************[Main.cc]
 Glucose -- Copyright (c) 2009-2014, Gilles Audemard, Laurent Simon
                                CRIL - Univ. Artois, France
                                LRI  - Univ. Paris Sud, France (2009-2013)
                                Labri - Univ. Bordeaux, France

 Syrup (Glucose Parallel) -- Copyright (c) 2013-2014, Gilles Audemard, Laurent Simon
                                CRIL - Univ. Artois, France
                                Labri - Univ. Bordeaux, France

Glucose sources are based on MiniSat (see below MiniSat copyrights). Permissions and copyrights of
Glucose (sources until 2013, Glucose 3.0, single core) are exactly the same as Minisat on which it 
is based on. (see below).

Glucose-Syrup sources are based on another copyright. Permissions and copyrights for the parallel
version of Glucose-Syrup (the "Software") are granted, free of charge, to deal with the Software
without restriction, including the rights to use, copy, modify, merge, publish, distribute,
sublicence, and/or sell copies of the Software, and to permit persons to whom the Software is 
furnished to do so, subject to the following conditions:

- The above and below copyrights notices and this permission notice shall be included in all
copies or substantial portions of the Software;
- The parallel version of Glucose (all files modified since Glucose 3.0 releases, 2013) cannot
be used in any competitive event (sat competitions/evaluations) without the express permission of 
the authors (Gilles Audemard / Laurent Simon). This is also the case for any competitive event
using Glucose Parallel as an embedded SAT engine (single core or not).


--------------- Original Minisat Copyrights

Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 **************************************************************************************************/

#include <errno.h>

#include <signal.h>
#include <zlib.h>
#include <sys/resource.h>

#include "utils/System.h"
#include "utils/ParseUtils.h"
#include "utils/Options.h"
#include "core/Dimacs.h"
#include "simp/SimpSolver.h"

using namespace Glucose;

//=================================================================================================

static const char* _certified = "CORE -- CERTIFIED UNSAT";

void printStats(Solver& solver){
    double cpu_time = cpuTime();
   //double mem_used = memUsedPeak();
   // (solving_state, probeTime, cpu_time, decisions, conflicts, #gCluases, averageLBD, GLR, inc)
   printf("%d %f %f %"PRIu64" %"PRIu64" %"PRIu64" %f %"PRIu64" %f %f %"PRIu64" %f %"PRIu64" %"PRIu64" %"PRIu64" %"PRIu64" %"PRIu64" %f %f %"PRIu64" %f %"PRIu64" %"PRIu64"\n"
   ,solver.state
   , cpu_time
   , solver.explorationOverhead
   , solver.starts
   ,  solver.decisions
   , solver.propagations
   , (double)solver.propagations / (double) solver.decisions
   , solver.conflicts
   , (double)solver.conflicts / (double) solver.decisions
   , (double)solver.totalLBD / (double) solver.conflicts
   , solver.numGlueClauses
   , (double) solver.numGlueClauses / (double) solver.conflicts
   , solver.numExpEpisodes
   , solver.numExpSteps
   , solver.numMissedExpSteps
   , solver.numExpConflicts
   , solver.expGlueClauses
   , (double) solver.numExpConflicts / (double) solver.numExpSteps
   , (double) solver.expTotalLBD / (double) solver.numExpConflicts
   , solver.CDPhaseCount 
   , (double) solver.totalCDPhaseLen / (double) solver.CDPhaseCount
   , solver.expInc
   , solver.topReplaced);
}



static Solver* solver;
// Terminate by notifying the solver and back out gracefully. This is mainly to have a test-case
// for this feature of the Solver as it may take longer than an immediate call to '_exit()'.
static void SIGINT_interrupt(int signum) {  
    solver->state = -1;
    printStats(*solver);
    exit(1); 
}   
    //solver->interrupt(); }

// Note that '_exit()' rather than 'exit()' has to be used. The reason is that 'exit()' calls
// destructors and may cause deadlocks if a malloc/free function happens to be running (these
// functions are guarded by locks for multithreaded use).
static void SIGINT_exit(int signum) {
    printf("\n"); printf("*** INTERRUPTED ***\n");
    if (solver->verbosity > 0){
        printStats(*solver);
        printf("\n"); printf("*** INTERRUPTED ***\n"); }
    _exit(1); }


//=================================================================================================
// Main:

int main(int argc, char** argv)
{
    try {
      //printf("c\nc This is glucose 4.1 --  based on MiniSAT (Many thanks to MiniSAT team)\nc\n");


      setUsageHelp("c USAGE: %s [options] <input-file> <result-output-file>\n\n  where input may be either in plain or gzipped DIMACS.\n");


#if defined(__linux__)
        fpu_control_t oldcw, newcw;
        _FPU_GETCW(oldcw); newcw = (oldcw & ~_FPU_EXTENDED) | _FPU_DOUBLE; _FPU_SETCW(newcw);
        //printf("c WARNING: for repeatability, setting FPU to use double precision\n");
#endif
        // Extra options:
        //
        IntOption    verb   ("MAIN", "verb",   "Verbosity level (0=silent, 1=some, 2=more).", 0, IntRange(0, 2));
        BoolOption   mod   ("MAIN", "model",   "show model.", false);
        IntOption    vv  ("MAIN", "vv",   "Verbosity every vv conflicts", 10000, IntRange(1,INT32_MAX));
        BoolOption   pre    ("MAIN", "pre",    "Completely turn on/off any preprocessing.", true);
        StringOption dimacs ("MAIN", "dimacs", "If given, stop after preprocessing and write the result to this file.");
        IntOption    cpu_lim("MAIN", "cpu-lim","Limit on CPU time allowed in seconds.\n", INT32_MAX, IntRange(0, INT32_MAX));
        IntOption    mem_lim("MAIN", "mem-lim","Limit on memory usage in megabytes.\n", INT32_MAX, IntRange(0, INT32_MAX));
 //       BoolOption opt_incremental ("MAIN","incremental", "Use incremental SAT solving",false);

         BoolOption    opt_certified      (_certified, "certified",    "Certified UNSAT using DRUP format", false);
         StringOption  opt_certified_file      (_certified, "certified-output",    "Certified UNSAT output file", "NULL");
         BoolOption    opt_vbyte             (_certified, "vbyte",    "Emit proof in variable-byte encoding", false);

         IntOption    mWDefault("MAIN", "mWDefault","Default value for mW.\n", 5, IntRange(1, INT32_MAX));
         IntOption    mSDefault("MAIN", "mWDefault","Default value for mS.\n", 5, IntRange(1, INT32_MAX));
         IntOption    prThDefault("MAIN", "prThDefault","Default value for prTh\n.\n", 2, IntRange(1, INT32_MAX));
         

        parseOptions(argc, argv, true);

        SimpSolver  S;
        double      initial_time = cpuTime();

        S.parsing = 1;
        S.use_simplification = pre;

        //if (!pre) S.eliminate(true);

        S.verbosity = verb;
        S.verbEveryConflicts = vv;
        S.showModel = mod;
        
        S.mWDefault = mWDefault;
        S.mSDefault = mSDefault;
        S.prThDefault= prThDefault;

        S.certifiedUNSAT = opt_certified;
        S.vbyte = opt_vbyte;
        if(S.certifiedUNSAT) {
            if(!strcmp(opt_certified_file,"NULL")) {
                S.vbyte =  false;  // Cannot write binary to stdout
                S.certifiedOutput =  fopen("/dev/stdout", "wb");
                if(S.verbosity >= 1)
                    printf("c\nc Write unsat proof on stdout using text format\nc\n");
            } else
                S.certifiedOutput =  fopen(opt_certified_file, "wb");
                const char *name = opt_certified_file;
                if(S.verbosity >= 1)
                    printf("c\nc Write unsat proof on %s using %s format\nc\n",name,S.vbyte ? "binary" : "text");
        }

        solver = &S;
        // Use signal handlers that forcibly quit until the solver will be able to respond to
        // interrupts:
        signal(SIGINT, SIGINT_exit);
        signal(SIGXCPU,SIGINT_exit);


        // Set limit on CPU-time:
        if (cpu_lim != INT32_MAX){
            rlimit rl;
            getrlimit(RLIMIT_CPU, &rl);
            if (rl.rlim_max == RLIM_INFINITY || (rlim_t)cpu_lim < rl.rlim_max){
                rl.rlim_cur = cpu_lim;
                if (setrlimit(RLIMIT_CPU, &rl) == -1){
                   // printf("c WARNING! Could not set resource limit: CPU-time.\n");
                }
            } }

        // Set limit on virtual memory:
        if (mem_lim != INT32_MAX){
            rlim_t new_mem_lim = (rlim_t)mem_lim * 1024*1024;
            rlimit rl;
            getrlimit(RLIMIT_AS, &rl);
            if (rl.rlim_max == RLIM_INFINITY || new_mem_lim < rl.rlim_max){
                rl.rlim_cur = new_mem_lim;
                if (setrlimit(RLIMIT_AS, &rl) == -1){
                    //printf("c WARNING! Could not set resource limit: Virtual memory.\n");
                }
            } }

        /*if (argc == 1)
            printf("c Reading from standard input... Use '--help' for help.\n");*/

        gzFile in = (argc == 1) ? gzdopen(0, "rb") : gzopen(argv[1], "rb");
        if (in == NULL)
            printf("ERROR! Could not open file: %s\n", argc == 1 ? "<stdin>" : argv[1]), exit(1);
        printf("%s ",argv[1]);
            
      if (S.verbosity > 0){
            printf("c ========================================[ Problem Statistics ]===========================================\n");
            printf("c |                                                                                                       |\n"); }

        FILE* res = (argc >= 3) ? fopen(argv[argc-1], "wb") : NULL;
        parse_DIMACS(in, S);
        gzclose(in);

       if (S.verbosity > 0){
            printf("c |  Number of variables:  %12d                                                                   |\n", S.nVars());
            printf("c |  Number of clauses:    %12d                                                                   |\n", S.nClauses()); }

        double parsed_time = cpuTime();
        if (S.verbosity > 0){
            printf("c |  Parse time:           %12.2f s                                                                 |\n", parsed_time - initial_time);
            printf("c |                                                                                                       |\n"); }

        // Change to signal-handlers that will only notify the solver and allow it to terminate
        // voluntarily:
        signal(SIGINT, SIGINT_interrupt);
        signal(SIGXCPU,SIGINT_interrupt);

        S.parsing = 0;
        if(pre/* && !S.isIncremental()*/) {
	 // printf("c | Preprocesing is fully done\n");
	  S.eliminate(true);
        double simplified_time = cpuTime();
        if (S.verbosity > 0){
            printf("c |  Simplification time:  %12.2f s                                                                 |\n", simplified_time - parsed_time);
 }
	}
	//printf("c |                                                                                                       |\n");
        if (!S.okay()){
            if (S.certifiedUNSAT) fprintf(S.certifiedOutput, "0\n"), fclose(S.certifiedOutput);
            if (res != NULL) fprintf(res, "UNSAT\n"), fclose(res);
            if (S.verbosity > 0){
 	        printf("c =========================================================================================================\n");
               printf("Solved by simplification\n");
                printStats(S);
                printf("\n"); }
            printf("s UNSATISFIABLE\n");
            exit(20);
        }

        if (dimacs){
            if (S.verbosity > 0)
                printf("c =======================================[ Writing DIMACS ]===============================================\n");
            S.toDimacs((const char*)dimacs);
            if (S.verbosity > 0)
                printStats(S);
            exit(0);
        }

        vec<Lit> dummy;
        lbool ret = S.solveLimited(dummy);
        S.state = ret==l_True ? 1 : (ret==l_False ? 0 : -1);        
        if (S.verbosity >= 0){
            printStats(S);
            //printf("\n"); 
        }
        //printf(ret == l_True ? "s SATISFIABLE\n" : ret == l_False ? "s UNSATISFIABLE\n" : "s INDETERMINATE\n");

        if (res != NULL){
            if (ret == l_True){
                printf("SAT\n");
                for (int i = 0; i < S.nVars(); i++)
                    if (S.model[i] != l_Undef)
                        fprintf(res, "%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
                fprintf(res, " 0\n");
            } else {
	      if (ret == l_False){
		fprintf(res, "UNSAT\n");
	      }
	    }
            fclose(res);
        } else {
	  if(S.showModel && ret==l_True) {
	    printf("v ");
	    for (int i = 0; i < S.nVars(); i++)
                if (S.model[i] != l_Undef)
		printf("%s%s%d", (i==0)?"":" ", (S.model[i]==l_True)?"":"-", i+1);
              printf(" 0\n");
	  }


        }


#ifdef NDEBUG
        exit(ret == l_True ? 10 : ret == l_False ? 20 : 0);     // (faster than "return", which will invoke the destructor for 'Solver')
#else
        return (ret == l_True ? 10 : ret == l_False ? 20 : 0);
#endif
    } catch (OutOfMemoryException&){
	        printf("c =========================================================================================================\n");
        printf("INDETERMINATE\n");
        exit(0);
    }
}
