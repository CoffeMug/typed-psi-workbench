
.PHONY: dist

dist:
	tar Ccvf .. PsiWorkBench.tar PsiWorkBench/src  PsiWorkBench/examples PsiWorkBench/tools PsiWorkBench/README PsiWorkBench/COPYRIGHT
	gzip PsiWorkBench.tar
