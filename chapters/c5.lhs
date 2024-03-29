%include polycode.fmt

\chapter{On (Fragmented) Usage Environments}

A usage environment appears in light of the subtleties in the fundamental
notion of ``consuming'' a linearly-bound variable: syntatically using a
variable does not necessarily mean that variable is consumed.
Specifically, in Linear Core, there are two situations in which the syntactic
use of a variable does not entail consuming it
\begin{itemize}
\item In lazy let bindings, since only when the binder is forced will we
consume the linear variables used in the binding
\item In case expressions, since only when either all linear components of the
pattern or the case binder are consumed do we actually consume the scrutinee
\end{itemize}


% --------------------------------------------------------------------------------

Originally, we had thought that in each case alternative there might appear
either all the linearly-bound variables in the pattern, or the case binder.
We type checked this by having all linearly-bound variables in the pattern be
exactly that, linearly bound variables, while the case-binder was a
$\Delta$-bound variable, and its usage environment were all the linear
variables from the pattern. This meant we needed to use either the case binder,
or the linear pat variables in the case alternatives (the case binder and the
linear pattern variables were mutually exclusive).
When faced with the
binder-swap transformation, we realized the typing rule wasn't general enough,
and: we needed to substitute occurrences of the scrutinee variables, which
should be able to occur in the DEFAULT alternative, by the case-binder.
So we needed the usage environment of the scrutinee to be availble in
the DEFAULT alternative, and this further complicated the rule.

Essentially, the case-binder had to have one distinct usage environment per
alternative, and in the DEFAULT alternative it had to have the scrutinee usage
environment. If this weren't complicated enough, we had to pass the usage
environments of the alternatives outside of the alternatives through
annotations to make sure the case-binder was annotated with the right
pat-variables. One good thing about this approach is that in case alternatives
in which there are no linearly bound variables, the usage environment of the
case-binder would be empty meaning we could use it unrestrictedly.

The final stop to this complicated rule was the reverse-binder-swap
transformation, which substituted occurrences of the case-binder in the
alternatives by a scrutinee variable. Since the case-binder could occur in any
alternative, while the scrutinee could only occur in the DEFAULT alternative,
the reverse-binder-swap optimisation didn't preserve the type of the
expression. But we came up with a new way to typecheck cases that is more
general, simpler, more uniform, and accepts the reverse-binder-swap.

The great insight to type cases better was born from the observation that the
case expression isn't all too different from the let expression (and we want
uniformity) -- the \textbf{fragmented usage environments}: In lets, we don't
consume the variables used in the body of the binder... because they're /not/
consumed until the binder is forced. Similarly, the case expression does /not/
consume the scrutinee (unlike what we were doing while trying to paper it
over)! In fact, all alternatives should have access to the same linear
variables required to type-check the scrutinee, just like the body of the let
has access to the linear variables required to type-check the binder body.

The only issue in passing the scrutinee environment to all case alternatives,
is that in those which linearly-bind pattern variables, we need some way to
specify that all linear pattern variables have to be consumed for the scrutinee
to be consumed. In restrospect it is obvious: the connection between those
variables and the scrutinee usage environment is more general than mutually
exclusivity between them and the case binder -- each linear variable in the
pattern contributes a fraction/fragment of the usage environment, and using
them all gets us a /complete/ usage environment, while using some is an
underusage of the usage environment, and using some and the case binder gets us
an overusage of the usage environment, and neither of the latter typecheck.
In short,
\begin{itemize}
\item The case-binder now has the same usage-environment across alternatives,
and the usage environment is the linear variables used to type-check the
scrutinee -- which are also available in all the alternatives, unlike before.
\item The DEFAULT alternative still gets the scrutinee-usage-environment, but its no longer a special case
\item For the patterns, each linear bound variable has a \emph{fraction/fragment} of the usage environment of the scrutinee.
\end{itemize}
Using the type-system notation, we have:
\[
\begin{array}{c}
  \infer*[right=(Case)]
  {\G,\D_s \vdash e : \s \and \hasnolinearvars{\G} \and \ov{\G',\D_s,\z[\D_s][\s] \vdash_{alt} \rho_i \to e_i :_{\D_s} \s \Longrightarrow \vp}}
  {\G,\G',\D_s \vdash \ccase{e}{\z[\D_s][\s]~\{\ov{\rho_i \to e_i}\}} : \vp}
\\[1em]
  \infer*[right=(Alt)]
  {\G, \ov{\x[\pi][\s]}[\frac{1}{n}\D_s/1,p] \vdash e_i : \s \and n=\setcardinality{\ov{\x[\pi][\s]}}}
  {\G \vdash K~\ov{\x[\pi][\s]} \to e_i :_{\D_s} \s \Longrightarrow \vp}
\\[1em]
  \infer*[right=($Alt_\_$)]
  {\G \vdash e_i : \vp}
  {\G \vdash \_ \to e_i :_{\D_s} \s \Longrightarrow \vp}
\end{array}
\]

Unfortunately, this undoes a feature of the previous system: in alternative
patterns with /no/ linear variables, the pattern is already consumed, so the
scrutinee variables should be consumed (no longer available, the fragment isn't
well-defined), and using the case-binder should consumes no extra resources,
since the data constructors can be used unrestrictedly. Even worse, as we've
hinted to, the above fractions aren't well defined if $n=0$. 

The solution is to consider the case $n=0$ separately, so we get both only
well-defined fragments, unrestricted case-binders in alternatives where there
are no linear variables, and the scrutinee variables are consumed. In the case
$n=0$, instead of assigning a fragment of the usage environment to each linear
variable, we substitute in the context occurrences of the usage environment by
nothing ($\cdot$), i.e. we delete the usage environment.
That entails two rules for $Alt$, instead of the one shown above:
\[
\begin{array}{c}
  \infer*[right=($Alt_n$)]
  { \G, \ov{\x[\pi][\s]}[\frac{1}{n}\D_s/1,p] \vdash e_i : \s \and n=\setcardinality{\ov{\x[\pi][\s]}} \and n>0 }
  { \G \vdash K~\ov{\x[\pi][\s]} \to e_i :_{\D_s} \s \Longrightarrow \vp }
\\[1em]
  \infer*[right=($Alt_0$)]
  { \G[\cdot/\D_s], \ov{\x[\pi][\s]} \vdash e_i : \s \and \setcardinality{\ov{\x[\pi][\s]}}=0 }
  {\G \vdash K~\ov{\x[\pi][\s]} \to e_i :_{\D_s} \s \Longrightarrow \vp}
\end{array}
\]
In substituting $[\cdot/\D_s]$, the case-binder $\z[\D_s][\s]$ will become
$\z[\cdot][\s]$, which is equivalent to an unrestricted variable
$\z[\omega][\s]$, and $\G,\D_s$ becomes $\G,\cdot$.

Finally, the description of how the patterns are typed becomes
\begin{itemize}
\item For the patterns in which linear pattern variables are bound, each linear variable has a \emph{fraction/fragment} of the usage environment of the scrutinee.
\item In patterns in which there are no bound linear variables, the usage-environment is deleted from the context (including from variable usage environments)
\end{itemize}

PS: Reminds me of separation logic fragments.

% TODO What happens if the data constructor is nullary? we need to check , and
% substitute Γ'[\cdot/\Delta_s] in the case |x:po| == 0

\section{Second attempt}

A usage environment is intrisically connected to the notion of suspended
computation. ... a variable annotated with a usage environment will consume that
usage environment when it itself is consumed -- because to consume that
variable we need to evaluate it, which forces evaluation of the suspended
computation, consuming the suspended resources...

In let, we don't need to annotate the $\delta$ vars in the usage environment of
the binder since they can occur \emph{instead} of the new $\delta$ var, since
they both refer to the resources their suspended computation consumes, and
either computation can happen. It doesn't make sense to add the $\delta$ vars
to the usage environments -- they're not exactly resources (but can only be
used once since they are associated to linear resources) -- only aliases to
computations that consume resources...

In a let binder, the resources from the proof-irrelevant linear context used in
the body of the binder are added to the usage environment of the binder
alongside the resources used from the linear context.

The above paragraph is just wrong. We need to differentiate between the
proof-irrelevant context and the relevant one in the usage envr....
%
Consider this example:
\begin{code}
f x y = let w = use x y (D={x,y})
         in case h x y of
              K a b -> [D]={x,y}
                return w
\end{code}
If we don't differentiate between the proof-relevant and irrelevant contexts,
then we can use `w` freely in the body of the case, and effectively consume `x`
and `y` from the linear context again.

Therefore, in each let, we need to store the irrelevant and the relevant usage
environment, and in the var rules we can only instantiate from the right one.
That is, let binders know if the resources used in their body came from the
irrelevant or relevant context.

Note that in usage environments we don't (and couldn't easily) differentiate
between the resources that will be consumed from the linear context and those
consumed from the proof irrelevant linear context. Linear resources can only be
in one of these contexts at the same time (we move from the linear to the proof
irrelevant when we evaluate an expression that's not in WHNF -- and can never
move these propositions back to the linear environment), and $\delta$ vars are
instantiated using the resources available in both contexts. Put simply, the
linear resource and proof irrelevant contexts are mutually exclusive, in that a
linear resource can only appear in one of them at the time, so $\delta$
variables can simply record the variables they used, and when instantiated will
use them from whichever context they're available from.

In let recs we need the mutually recursive lets to be strongly connected. If
the letrec binds are strongly connected, then the usage environment of all
binders will be the same.

\section{Case Expressions}

Case expressions evaluate their scrutinees to weak head normal form (WHNF). The
process of evaluation is what actually consumes linear resources, according to
the definition of consuming a resource (in our case, that's the definition given in Linear Haskell):

Definition 2.1 (Consume exactly once).
\begin{itemize}
\item To consume a value of atomic base type (like Int or Ptr) exactly once, just evaluate it.
\item To consume a function value exactly once, apply it to one argument, and consume its result
exactly once.
\item To consume a pair exactly once, pattern-match on it, and consume each component exactly
once.
\item In general, to consume a value of an algebraic datatype exactly once, pattern-match on it,
and consume all its linear components exactly once (Sec. 2.5)1.
\end{itemize}

This definition drives the entire story of linear resource consumption and the
rules that treat linear resources in a way different from intuitinistic linear logic.
In particular, we're concerned with the interaction between call-by-need
evaluation, suspended computations, evaluation of expressions to WHNF, and
their relationship with the effective consumption of resources...

In fact, one can imagine defining a linear core parametrized over X, where X is
the operational semantics of evaluation/definition of consuming resources
according to the evaluation semantics. Say, LinearCore(X), as HM(X) and
OutsideIn(X).

It seems that the consumption of resources is deeply connected to evaluation.
\emph{When we evaluate expressions we consume the linear resources used in that
expression}.

In a call-by-need language, a let-binding defines a suspended computation that
\emph{won't consume the resources it requires until it is actually run}. When
the binder is \emph{fully} evaluated, the resources used in the computation will have
be consumed, and then the result of the computation, which is bound to the same
binder that was evaluated, must be consumed linearly too.

Evaluation, however, in languages like Haskell (what kind are these?), doesn't
entail \emph{fully} evaluating the expression. Rather, evaluation entails
reducing an expression to Weak Head Normal Form (WHNF).
%
When reasoning about resource consumption, evaluation of an expression to WHNF
makes it unclear which resources were actually consumed.
%
Since we can't know exactly which resources will be consumed when an expression
is evaluated to WHNF (intuitively it seems obvious, but why can't we
precisely?), we must consider all resources to no longer available, but
simultaneously that none of them might have been consumed, and we must
guarantee that the result is evaluated to NF (somewhere along the way here I
should mention NF up to linear fields) to finalize the consumption of resources
-- resources are only effectively consumed when the expression is fully
evaluated (i.e. evaluated to Normal Form (NF)).

For our Linear Core based on GHC Core, where X is the definition given above,
which defines consumption of resources in face of the non-strict evaluation
semantics of Haskell, we have specifically that:
\begin{itemize}
\item Evaluating an expression that's in Weak Head Normal Form (WHNF) doesn't consume any resources, since no computation takes place.
\item Evaluating an expression that's not in WHNF will consume resources, but
  we don't know exactly which.
  \begin{itemize}
  \item We must treat all of these resources uniformly as though they
    haven't yet been consumed (i.e. consume linearly-bound variables in the
    patterns to force the scrutinee to NF to guarantee all resources are
    consumed)
  \item We must simultaneously treat them as though they have already been consumed.
  \item We can do this by putting these resources in a proof-irrelevant linear context
    \begin{itemize}
    \item Resources from the proof-irrelevant linear context cannot be used directly
    \item Instead, $\delta$-bound variables can refer to resources in the proof-irrelevant linear context, and will consume it when they themselves are consumed.
    \end{itemize}
  \end{itemize}
\item Evaluating a variable is a special case, because the computation it represents might or might not be already evaluated to WHNF:
  \begin{itemize}
  \item Consume all the resources it is bound to (be it itself or other resources)
  \item Add itself as a linear resource that must be consumed (semantically, it means the result of the computation must be consumed linearly in the body of the case)
  \item The usage environment of the case is then the variable itself, and the split usage environment of pattern variables is the variable exactly
  \end{itemize}
\end{itemize}
Where "evaluation" happens when an expression is scrutinized by a case expression.

TODO Need to itemize this whole section in a succint summary at the end, or
even make a diagram... It is simply confusing and hard to identify distinct
concepts in this text.

\section{Mapping from Core to (mini) Linear Core}

How we get rid of type variables maybe, and of type schemes

\section{todos}

(TODO: That counter example that messes up fraction numbers will change the rules again...)

