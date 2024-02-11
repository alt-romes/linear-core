How to reproduce the plugin results:
===

1. Add `linear-core-prototype` to the dependencies of the package you want to
   validate
2. Add `-fplugin=Linear.Core.Plugin` to the `ghc-options` field of the package
   you want to validate
3. Add the following lines to the `cabal.project` file (if one did not exist,
   you must additionally have the line `packages: .`):
    ```
    ```
    source-repository-package
    type:     git
    location: https://github.com/alt-romes/linear-core.git
    subdir: prototype
    ```

Then...

1. Output `cabal build` into a file `output`, e.g. `cabal build lib:linear-base -j1 --allow-newer 2>&1 | tee output`
2. Print out total number of failures
    ```
    cat output | grep -A1 FAILED | grep -e '^  ' | wc
    ```
2. Print out number of unique failures
    ```
    cat output | grep -A1 FAILED | grep -e '^  ' | sort | uniq | wc
    ```
3. Print out total number of successes
    ```
    cat output | grep SUCCESS | awk '{print $2}' | paste -s -d+ | bc
    ```
