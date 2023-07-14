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

