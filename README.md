# Ideas

Perhaps we should only emit the usage environment once per binding. That way,
    if the binder is used, the binder's usage environment is consumed. If the
    binder is not used, then we do not emit the usage environment. If the binder
    is used twice, we only emit its usage environment once.

```haskell
let x = (y,z) in
case e of
    Pat1 -> ... x ...
    Pat2 -> ... y ... z
```

Upon finding the let we don't emit anything. Upon finding `x` in the first
branch we emit its usage environment (`y, z`). On the second branch, we emit
once `y` and once `z`. If we used `x` we would re-emit both `y, z` again.
However if we used `x` twice in the second branch we would still only emit `y, z`
once from the usage of `x` and once `y` and `z` individually.


