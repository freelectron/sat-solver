### Welcome to you SAT project for Knowledge Representation cour of VU Amsterdam 

Our code is written in *PYHON 3.7* we assume you have the interpreter installed.

Our code does *NOT* requre any custom build packages.

As we have six (different) heuristics we provide an option to run each of the six algorithms.

*PLEASE* note that the best performing heuristics are S5 and S6 (and it is not slow).

In order to run our solver with either of the heuristics, you could just type in your (bash) terminal:

	$ ./SAT.sh {-S1 or -S2 or-S3 -S4 or -S5 or -S6} {inputfilename.txt}

You could make a simple test by running:  
	
	$ ./SAT.sh -S6 inputfile_test.txt
