COMMON=-fforce-recomp -ddump-to-file -ddump-simpl -dno-typeable-binds -dcore-lint
err:
	ghc NameCache.hs -O2 $(COMMON) -dlinear-core-lint

ok:
	ghc NameCache.hs -O2 $(COMMON)
