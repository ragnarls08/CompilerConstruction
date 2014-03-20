all: bnfc haskell clean

haskell:
	ghc --make TestJavalette.hs -o TestJavalette
	ghc -O2 jlc.hs -o jlc
bnfc:
	bnfc Javalette.cf
	happy -gca ParJavalette.y
	alex -g LexJavalette.x

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DocJavalette.ps
	
distclean: clean
	-rm -f DocJavalette.* LexJavalette.* ParJavalette.* LayoutJavalette.* SkelJavalette.* PrintJavalette.* TestJavalette.* AbsJavalette.* TestJavalette ErrM.* SharedString.* Javalette.dtd XMLJavalette.* 




