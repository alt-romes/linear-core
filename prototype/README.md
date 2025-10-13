Overview
===

Linear Core is a type system that understands linearity in the presence of
laziness, unlike traditional type systems which fail to see linearity when
non-strictness makes it less apparent (e.g. by aliasing).

This interaction arises naturally in languages with both linearity and
non-strictness, or in linear strict languages with lazy features.

That said, our primary motivation is the intermediate language of the Glasgow
Haskell Compiler, called Core -- a language which not only combines linearity
with laziness, but also aggressively transforms these programs during the
optimisation passes.

In fact, Core's linear type system cannot understand linearity soon after
optimisations start being applied because they transform the program in a way
which makes linearity no longer syntactic, but still valid. The compiler
optimisations should never turn a linear program into a non-linear one, and
being able to validate linearity throughout the optimisation pipeline, like it
does types, is invaluable as a sanity-check to identify and prevent bugs.
At the moment, the linearity information is simply thrown away before
optimisations.

Claims
===

Our artifact contains a prototype implementation of Linear Core as a plugin for
the Glasgow Haskell Compiler (GHC). The plugin validates the linearity, according to
Linear Core, at the start of every optimisation pass, of every intermediate
program. It will never interrupt compilation, simply printing FAILED when an
intermediate program is not accepted by our implementation of Linear Core.

We believe Linear Core is a good target for the intermediate language of GHC
because, while being an extension of the existing intermediate language, can
reconcile linearity and laziness in a way robust to all optimisations carried
out by GHC. Our prototype displayed this in practice by accepting almost every
program produced by the GHC pipeline, while rejecting very few -- including
identifying programs which are truly invalid.

We claim our prototype accepts the vast majority of programs produced by the
compiler when compiling linearity-heavy Haskell libraries (over 99% of
intermediate programs from the libraries we tested it on).

Installation
===

Installation requires an installation of GHC 9.10. We recommend downloading it using [GHCup](https://www.haskell.org/ghcup/):
```
export BOOTSTRAP_HASKELL_GHC_VERSION=9.10.3
curl --proto '=https' --tlsv1.2 -sSf https://get-ghcup.haskell.org | sh
```

Make sure it succeeded and that cabal packages are up to date by running:
```
ghc --version
cabal --version
cabal update
```

Second, we need to download the packages we want to test using the `linear-core-prototype` plugin.
We tested the plugin on the largest open linear Haskell packages we found: [`linear-base`](https://github.com/tweag/linear-base), [`priority-sesh`](https://github.com/wenkokke/priority-sesh), [linear-smc](https://github.com/jyp/linear-smc)

How to reproduce the plugin results
===

Let's reproduce the results individually for the three packages. Note: the
numbers will not match exactly due to changes in the compiler since the numbers
were first produced, but the vast majority of intermediate programs should be
accepted and only few rejected.

### linear-base

1. Fetch the source

```
cabal get linear-base-0.5.0
cd linear-base-0.5.0
```

2. Add the plugin to `linear-base.cabal`:
```diff
diff --git a/linear-base.cabal b/linear-base.cabal
index efab84d..4f7a57e 100644
--- a/linear-base.cabal
+++ b/linear-base.cabal
@@ -144,6 +144,8 @@ library
         transformers,
         vector >=0.12.2,
         primitive
+    build-depends: linear-core-prototype == 0.1.0.0
+    ghc-options: -fplugin=Linear.Core.Plugin
 
 library examples
     import: build-opts
```

3. Build the package and pipe to `output`:

```
cabal build linear-base 2>&1 | tee output
```

4. Compute the metrics:
```
echo "TOTAL REJECTED:"
cat output | grep -A1 FAILED | grep -e '^  ' | wc -l

echo "UNIQUE REJECTED:"
cat output | grep -A1 FAILED | grep -e '^  ' | sort | uniq | wc -l

echo "TOTAL ACCEPTED"
grep SUCCESS output | awk '{print $2}' | tr '\n' '+' | sed 's/+$//' | bc
```

### linear-smc

As above, but for a different package:

1. Fetch the source
```
cabal get linear-smc-2.2.3
cd linear-smc-2.2.3
```

2. Add the plugin to `linear-base.cabal`:
```diff
diff --git a/linear-smc.cabal b/linear-smc.cabal
index d3d3226..f76eae3 100644
--- a/linear-smc.cabal
+++ b/linear-smc.cabal
@@ -83,6 +83,8 @@ library
     build-depends: constraints >= 0.13.4 && < 666
     build-depends: array >= 0.5 && < 666
     build-depends:    base >=4.16.4.0 && < 666
+    build-depends: linear-core-prototype == 0.1.0.0
+    ghc-options: -fplugin=Linear.Core.Plugin
 
     -- Directories containing source files.
     hs-source-dirs:   .
```

3. Build the package and pipe to `output`:
```
cabal build linear-smc 2>&1 | tee output
```

4. Compute the metrics:
```
echo "TOTAL REJECTED:"
cat output | grep -A1 FAILED | grep -e '^  ' | wc -l

echo "UNIQUE REJECTED:"
cat output | grep -A1 FAILED | grep -e '^  ' | sort | uniq | wc -l

echo "TOTAL ACCEPTED"
grep SUCCESS output | awk '{print $2}' | tr '\n' '+' | sed 's/+$//' | bc
```

### priority-sesh

1. Fetch sources
```
git clone https://github.com/wenkokke/priority-sesh.git
cd priority-sesh
```

2. Add the plugin
```diff
diff --git a/priority-sesh.cabal b/priority-sesh.cabal
index 28b51ac..12b3aba 100644
--- a/priority-sesh.cabal
+++ b/priority-sesh.cabal
@@ -40,6 +40,8 @@ library
                     , Data.Type.Priority
                     , System.IO.Linear.Cancellable
   hs-source-dirs:     src
+  build-depends: linear-core-prototype == 0.1.0.0
+  ghc-options: -fplugin=Linear.Core.Plugin
 
 test-suite test-priority-sesh
   import:             common-depends
```

3. Build the package
```
cabal build priority-sesh --allow-newer=linear-base 2>&1 | tee output
```

4. Compute the metrics with the same commands as above

How to reproduce the plugin results in its general form:
===

1. Add `linear-core-prototype` to the `build-depends` of the package you want to
   validate
2. Add `-fplugin=Linear.Core.Plugin` to the `ghc-options` field of the package
   you want to validate

1. Output `cabal build` into a file `output`, e.g. `cabal build lib:linear-base -j1 2>&1 | tee output`
2. Print out total number of failures
    ```
    cat output | grep -A1 FAILED | grep -e '^  ' | wc -l
    ```
2. Print out number of unique failures
    ```
    cat output | grep -A1 FAILED | grep -e '^  ' | sort | uniq | wc -l
    ```
3. Print out total number of successes
    ```
    grep SUCCESS output | awk '{print $2}' | tr '\n' '+' | sed 's/+$//' | bc
    ```

