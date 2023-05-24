
Questions for the call:



* In this example of the case-of-case transformation, why is the the former well
    typed but the latter not?
    ```haskell
      f :: a ⊸ b ⊸ (a, b)

      case (case u of w[1]
                (x[1], y[1]) -> f x y
            ) of w'[Many]
        (z[Many], t[Many]) -> z
      ==>
      case u of w[1]
        (x[1], y[1]) -> case f x y of w'[Many]
                          (z[Many], t[Many]) -> z

      ```
* Our system doesn't accept this, but we scale the binders when we do the
transformation.
Scaling vai ser importante, explicar que estas tranformações só estão bem definidas com scaling.


* How does the multiplicity of the case binder is currently inferred? This comes
    up in our rule for the case binder, as in the wildcard alt we need this
    inferred mult.

* Discuss our case alternative rule.
    <!-- * If the pattern is *linearly* incomplete (no--this is jsut wrong), then the case binder will have mult %p, -->
    <!--     while with complete patterns it has a usage environment containing each -->
    <!--     linear variable in the pattern. -->
    * In the case of the wildcard, the binder is lambda bound with the multiplicity inferred
    * In all other cases, z has usage env = linear vars of pattern,
    * Since otherwise a linearly-incomplete pattern would never be well-typed
        (can't say either z or a b c since a b c are already bound)

    ```haskell
    P :: α ⊸ β ⊸ ξ ⊸ P α β ξ
    case x of z:p
      P a b c -> ___ z:(a,b,c) && a:1 b:1 c:1
      P _ b c -> -- Non-linear pattern -- not well-typed
      _       -> ___ z:p -- In this branch we must use `z` `p` times, what's `p`
                         -- Usage env of $x$ wouldn't work either? It's hard...
    ```

* Discuss a group of let-rec binders must all share the same usage environment
    (implies group is minimal, which is not guaranteed always),
    and the parallelism with the free variables of a group of recursive binders
    (they all share the same FVs, I saw this explained in GHC somewhere)
    Even more so considering the usage environment is the linear subset of the
    free variables


* This example:
```haskell
-- Doesn't typecheck
-- Should this work with $z$?
f :: Int %1 -> IO ()
f x = case x of -- {z}
        _ -> case consumeInt' x of -- x has been forced, how is x != z
               () -> pure ()

-- Binder swap is applied in both directions, makes x <-> z. x must be a var
-- Both if we use x and z we have well-typed programs,
-- Type-checker isn't stable by substitution (no way around for now...)
```

If we used the `z` binder instead of `x`, would this be will typed? How is `x`
different from `z`? In our rule, `z` would have to be used. `x` and `z` are
names for the same thing, but the name `x` has been used?

```haskell
f = do
    ptr <- malloc 4
    ptr' <- writePtr 5 ptr
    -- how is ptr /= from ptr'

```
* How to handle join points? They seem to be compared to let-recs very often,
    how can we prove things for them through let-recs? Or should we consider
    them in our proofs?
    * There are recursive vs non-recursive join points
    * In Minicore the rules for let work for join points as well
        * We will want to do something like that too
    * Great source of let-recs with free-vars
    * Most of the code treats them like lets
    * Just a tag on the variable whether its join point or not

* Discuss the binding site In practice, there seem to be more than lambda and let bound.
    * There are
        * Lambda Bound
        * Let Bound
        * Case Bound
        * Case Pattern Bound -- This is in practice the same as lambda bound
    * Why did you previously consider case binders to be lambda bound?
    * This shows up in the datatype `BindingSite`
    * In the datatype `PatCtxt` we consider patterns in case alts and such
        lambda bound, and only let(rec) things let-bound.

* Provenence in patterns. In Note [Typechecking pattern bindings] it is said we
    use newLetBndr for all pattern-bound variables, this would be wrong:
    ```haskell
    -- f is let bound
    -- a and b are lambda bound
    let f a b = a + b
     in ...
    ```

    IdBin

    * Look at `tcPatBndr` a bit on call if possible, and if `PatCtxt` means
        anything or is discrepant with our idea of let-bound



<!-- Para um tipo algébrico diferente, com construtores lineares e não lineares -->
<!-- Como é que no wildcard isto faz sentido? -->


* What are the semantics of Scaled? Can I have a Scaled Let-bound var? It seemed
    initially we only scaled pat-bound vars and lamb-bound vars...






Call Notes
----------
```haskell
    P :: a ⊸ b ⊸ c ⊸ P a b c
    case_omega x of z:p
      [a,b,c] P a b c -> z:[a,b,c] || a ^ b ^ c
      _       -> ___ z:p

    case_omega (x,y) of z:omega
        (x[omega], y[omega]) -> x
```

In Linear Haskel, unlike LL, we have this isomorphism
(Ur x, Ur y) -> Ur (x , y)
Ur (x , y)  -> (Ur x, Ur y)
(Consequence of case_omega)

Multiplicities in case binders:
* Always inferred in the frontend

* The letrec (inferrence) exception is because letrecs are generated by Core


case_p
map :: (a %p -> b) -> [a] %p -> [b]


InScope set map from names to variables, used for substitution propagating
things




Call Notes 2
============

```haskell
    case_1 w of z:1
        (x[1], y[1]) -> (x,y) -- use x,y

    case_1 w of z:1
        (x[1], y[1]) -> z     -- use z[x,y]

    -- Isn't impossible, but do we even want it? Future work...
    case_1 Δ |- w of z:1
        (x[1], y[1]) -> w -- should be just like case (2)

    case_1 Δ |- <expr> of z:1
        (x[1], y[1]) -> Δ || x,y || z
```

Q1: Does binder-swap occur in case alternatives other than wildcard?
A1: Yes! It does happen in all alternatives...



# 24 May

Found:

Note [Floating linear case]
___________________________
Linear case can't be floated past case branches:
    case u of { p1 -> case[1] v of { C x -> ...x...}; p2 -> ... }
Is well typed, but
    case[1] v of { C x -> case u of { p1 -> ...x...; p2 -> ... }}
Will not be, because of how `x` is used in one alternative but not the other.

It is not easy to float this linear cases precisely, so, instead, we elect, for
the moment, to simply not float linear case.
