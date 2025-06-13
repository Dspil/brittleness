mutants: mutants.rkt
	raco exe mutants.rkt

dist: mutants
	raco distribute mutator mutants

clean:
	rm mutants && rm -r mutator
