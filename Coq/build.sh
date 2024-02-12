# Arg 1 - takes the file to be compiled (full path). If not supplied, the .ds file to be compiled should be in the current directory (and the only .ds file in the directory).
coqdep -f _CoqProject > .coqdeps.d
coq_makefile -arg "-quiet" -f _CoqProject -o core.make 
make -f core.make