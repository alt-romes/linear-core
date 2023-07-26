{-

In essence, we have one unrestricted context, two linear contexts, and one
affine context. This matches the relationship between affine types and
call-by-need explored in~\cite{}.

What do we know about affine type systems that we can use in our system for the \deltas?

Notes from linear haskell:
Variables in the environments are annotated by a multiplicity (1 or ω), ω-variables are ordinary
variables. When forced, an ω-variable is replaced by its value (to model lazy sharing), but 1-
variables must be consumed exactly once: when forced, they are removed from the environment.
Reduction gets stuck if a 1-variable is used more than once.


On NF values:
f rw = case rw of
        RealWorld# -> ...?? rw has been consumed, what now? I suppose we can't make up RealWorld#s, only thread them?


On contexts:
Perhaps we can merge the proof irrelevant and linear contexts?
Dropping Γ no longer seems like that good of an idea, because it would conflate unrestricted with affine variables
Then again, delta vars with empty usage environments are really not affine... (either we move them, or give explicit contract)

On optimisations:
Don't forget to re-read the future-work section of Linear Haskell!

On the implementation:
How do we infer the proof-irrelevant linear context? How do we know what is in
the proof irrelevant context vs what isn't without typechecking?
Perhaps in the inference pass we carry a reader context mapping linear
resources to either the linear or proof irrelevant context, and update it in
cases expressions where the scrutinee is not in whnf.

Three relevant notes:
Note [Zero as a usage]
~~~~~~~~~~~~~~~~~~~~~~
In the current presentation usages are not exactly multiplicities, because they
can contain 0, and multiplicities can't.

Why do we need a 0 usage? A function which doesn't use its argument will be
required to annotate it with `Many`:

    \(x % Many) -> 0

However, we cannot replace absence with Many when computing usages
compositionally: in

    (x, True)

We expect x to have usage 1. But when computing the usage of x in True we would
find that x is absent, hence has multiplicity Many. The final multiplicity would
be One+Many = Many. Oops!

Hence there is a usage Zero for absent variables. Zero is characterised by being
the neutral element to usage addition.

We may decide to add Zero as a multiplicity in the future. In which case, this
distinction will go away.

Note [Joining usages]
~~~~~~~~~~~~~~~~~~~~~
The usage of a variable is defined, in Note [Usages], as the minimum usage which
can be ascribed to a variable.

So what is the usage of x in

    case … of
      { p1 -> u   -- usage env: u_ue
      ; p2 -> v } -- usage env: v_ue

It must be the least upper bound, or _join_, of u_ue(x) and v_ue(x).

So, contrary to a declarative presentation where the correct usage of x can be
conjured out of thin air, we need to be able to compute the join of two
multiplicities. Join is extended pointwise on usage environments.

Note [Bottom as a usage]
~~~~~~~~~~~~~~~~~~~~~~
What is the usage of x in

   case … of {}

Per usual linear logic, as well as the _Linear Haskell_ article, x can have
every multiplicity.

So we need a minimum usage _bottom_, which is also the neutral element for join.

In fact, this is not such as nice solution, because it is not clear how to
define sum and multiplication with bottom. We give reasonable definitions, but
they are not complete (they don't respect the semiring laws, and it's possible
to come up with examples of Core transformation which are not well-typed)

A better solution would probably be to annotate case expressions with a usage
environment, just like they are annotated with a type. Which, probably not
coincidentally, is also primarily for empty cases.

A side benefit of this approach is that the linter would not need to join
multiplicities, anymore; hence would be closer to the presentation in the
article. That's because it could use the annotation as the multiplicity for each
branch.

-}

{-
Handling Empty Case:

How do we type the following?

    f x =
       case … of {}

 -}
