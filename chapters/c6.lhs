%include polycode.fmt

% \chapter{Linear Core, again}
% 
% % Proof macros
% \input{language-v2/proof}
% 
% \input{language-v2/Syntax}
% 
% \clearpage
% \input{language-v2/TypingRules}
% 
% \chapter{Linear Core, again, again}
% 
% % Proof macros for v3
% \input{language-v3/proof}
% 
% \input{language-v3/Syntax}
% 
% \input{language-v3/TypingRules}
% 
% \input{language-v3/OperationalSemantics}

%\clearpage
% \section{Type Safety}

% \input{language-v3/proofs/TypePreservationTheorem}

% \input{language-v3/proofs/ProgressTheorem}

% \input{language-v3/proofs/LinearSubstitutionLemma}

% \input{language-v3/proofs/UnrestrictedSubstitutionLemma}
% 
% \input{language-v3/proofs/DeltaSubstitutionLemma}
% 
% \clearpage
% 
% TODO! Substitution of proof-irrelevant linear variables preserves typing. The
% term always remains the same because $x$ cannot occur in any term, however, all
% variables that refer to $x$ in their usage environment must now refer the usage env. of the substitee (e.g. $[x] => [\D]$).
% This seems trivial to see correct, since all occurrences are in environments, so we get some equivalence similar to the one we need for the proof of Alt0.
% 
% \begin{lemma}[Substitution of proof-irrelevant linear variables preserves typing]
% If $\judg[\G][\D,\irr{\x}][\d]{e}{\vp}$ and $\judg[\G][\D'][\d']{e'}{\s}$ then $\judg[\G][\D,\irr{\D'}][\subst{\d}{\D'}{x},\d']{e}{\vp}$
% \end{lemma}

% TODO: Multiplicity substitution preserves typing lemma
% 
% TODO: Canonical forms lemma
% 
% TODO: Corollary of $\Delta$-var subst. for $\ov{\Delta}$
% 
% TODO: Constructor app typing:
% If $\Gamma, \Delta \vdash K~\ov{e}$ and $K{:}\ov{\sigma\to\pi}~T~\ov{p} \in \Gamma$ and $\hasnolinearvars{\Gamma}$
% then $\ov{\Gamma, \Delta_i \vdash e_i : \sigma_i}$

% \clearpage

% \input{language-v3/InferUsageEnvs}

% \input{language-v3/proofs/optimizations/Inlining}
% \input{language-v3/proofs/optimizations/BetaReduction}
% \input{language-v3/proofs/optimizations/CaseOfKnownConstructor}
% \input{language-v3/proofs/optimizations/LetFloating}
% \input{language-v3/proofs/optimizations/CaseOfCase}
% \input{language-v3/proofs/optimizations/BinderSwap}

\chapter{Linear Core, again, again, again}

For this last version we get rid of the delta-affine context and make
delta-variables completely unrestricted, and remove the CaseVar transformation
which wasn't sound when beta-reduction for linear-lambdas interacted with the
reverse binder swap c.f. Chapter "Why I hate reverse-binder-swap".

No entanto, não parece ser uma limitação do sistema de tipos, mas sim uma
duplicação verdadeira de recursos, pela primeira vez.
Isso significa que temos de encontrar umas condições para as quais o reverse binder swap não é linear mesmo.

c.f. call-notes de 28-07

Ou seja, isto se calhar é uma falha verdadeira na transformação que pode duplicar recursos!
Open a ticket about it!
\begin{code}
(\x -> case x of _ -> x) (close h rw)
==>
case close h rw of _ -> close h
\end{code}

Write that, in practice, we have 4 contexts (2 linear, 2 unrestrited) + mult. var context

\begin{itemize}
\item Write ticket about unsoundness of reverse-binder-swap in face of beta-reduction without binding
\item On second thought, there's another way: We have two distinct linear type systems, one for optimisations and another for other linting.
      But the former system is much weaker, and won't trigger call-by-name
      beta-reduction on as many cases as the latter system can. However, it
      would be valid to have beta-reduction and case-var, since beta-reduction
      would still see the reverse binder swap as non-linear, so would still
      bind...
\end{itemize}


% Include all the other proof macros, so that the renewcommands work as
% expected (they were designed assuming things were already defined previously)
\input{proof}
\input{language-v2/proof}
\input{language-v3/proof}
% Proof macros for v4
\input{language-v4/proof}

\input{language-v4/Syntax}

\input{language-v4/TypingRules}

\input{language-v4/OperationalSemantics}
\clearpage

\section{Type Safety}

\input{language-v4/proofs/TypePreservationTheorem}

\input{language-v4/proofs/ProgressTheorem}

\input{language-v4/proofs/LinearSubstitutionLemma}

\input{language-v4/proofs/UnrestrictedSubstitutionLemma}

\input{language-v4/proofs/DeltaSubstitutionLemma}
 
\clearpage
TODO! Substitution of proof-irrelevant linear variables preserves typing. The
term always remains the same because $x$ cannot occur in any term, however, all
variables that refer to $x$ in their usage environment must now refer the usage env. of the substitee (e.g. $[x] => [\D]$).
This seems trivial to see correct, since all occurrences are in environments, so we get some equivalence similar to the one we need for the proof of Alt0.

\begin{lemma}[Substitution of proof-irrelevant linear variables preserves typing]
If $\judg[\G][\D,\irr{\x}][\d]{e}{\vp}$ and $\judg[\G][\D'][\d']{e'}{\s}$ then $\judg[\G][\D,\irr{\D'}][\subst{\d}{\D'}{x},\d']{e}{\vp}$
\end{lemma}

TODO: Multiplicity substitution preserves typing lemma

TODO: Canonical forms lemma

TODO: Corollary of $\Delta$-var subst. for $\ov{\Delta}$

TODO: Constructor app typing:
If $\Gamma, \Delta \vdash K~\ov{e}$ and $K{:}\ov{\sigma\to\pi}~T~\ov{p} \in \Gamma$ and $\hasnolinearvars{\Gamma}$
then $\ov{\Gamma, \Delta_i \vdash e_i : \sigma_i}$

\clearpage

% \input{language-v4/InferUsageEnvs}

% \input{language-v4/proofs/optimizations/Inlining}
% \input{language-v4/proofs/optimizations/BetaReduction}
% \input{language-v4/proofs/optimizations/CaseOfKnownConstructor}
% \input{language-v4/proofs/optimizations/LetFloating}
% \input{language-v4/proofs/optimizations/CaseOfCase}
% \input{language-v4/proofs/optimizations/BinderSwap}

\section{How reverse binder swap interacts with linearity}

\begin{itemize}
\item We can have a rule ($CaseVar$) to type cases of variables that still get used in its body
\item And type the reverse-binder-swap + the float-out that simon mentioned.
\item However, if we beta-reduce an expression that uses the case-var rule and does use $x$ in the case-alternatives, then we effectively duplicate resources.
\item This looks like a real bug, not a type system limitation. (The soundness proof for the language that had $CaseVar$ uncovered it)
\item c.f. examples in call-notes (28-07 mainly)
\item Great, we become uniform in that variables are considered not in WHNF
\item This might, however, be actually OK in Core - the occurrence analysis that determines whether beta-reduction can or cannot be call-by-name is different from the linear type-checker (which is an unfortunate non-uniformity -- our system can likely see much more things as being linear, but can't support reverse-binder-swap AND call-by-name-beta-reduction)
\end{itemize}

\section{The K-Vars Arrangement Dilemma}

Consider the reduction of case expressions for a known pattern,
\[
\ccase{K~\overline{e}}{z{:}_{\Delta}\sigma' \{\dots, K~\overline{x{:}_\pi\sigma} \to e'\}} \longrightarrow e'\overline{[e/x]}[K~\overline{e}/z]
\]
and the typing rule for $CaseWHNF$ and the alternatives $AltN$:
\[
\TypeCaseWHNF
\]
\[
\TypeAltNIncorrect
\]
When we add the constructor-bound variables to the context, we make them
$\Delta$-bound and assign a tag to each of the variables in their usage
environment (which is the usage env. of the scrutinee, modulo the tags).

The tags work great to ensure all the linear variables in the pattern are used
exactly once. In contrast, if we used simply fractions to fragment the usage
environment we could e.g. use two times the same pattern variable to use all
the resources. Tags are able to encode the idea that each pattern
positional-variable must be consumed once, even if they're pattern-matched on
multiple times, for example:
\begin{code}
f x y =
  case (x,y) of
    (a,b) -> case (x,y) of
      (n,p) -> (a,p)
\end{code}
is well-typed because we split $x,y$ into $x\#(,)1, x\#(,)2, y\#(,)1, y\#(,)2$, and
give to the pattern variables usage environments $\D_a = x\#(,)1, y\#(,)1$, $\D_b = x\#(,)2, y\#(,)2$, $\D_n
= x\#(,)1, y\#(,)1$, $\D_p = x\#(,)2, y\#(,)2$. (Really, we first assign the usage
environments, and are forced to Split the resources in order to use the pattern
variables).

However, this interacts badly with our substitution lemma for $\D$-vars:
If $\G;\D \vdash e' : \s$ and $\G,\xD;\D,\D' \vdash e : \vp$ then $\G; \D,\D' \vdash e[e'/x] : \vp$.
We'll want to substitute an expression for each pattern-variable (see above
reduction), but we'll have expressions using different resources for each
pattern while simultaneously have each pattern variable use a fragment of all
the resources used in the scrutinee. This doesn't allow us to use the
$\Delta$-substitution lemma.
An example makes this clear:
\begin{code}
f x y =
  case K x y of
    K a{x#K1,y#K1} b{x#K2, y#K2} -> (a, b)
\end{code}
We want to substitute $[x/a]$ and $[y/b]$, however, a doesn't have u.e. = $x$
and b doesn't have u.e. equal to $y$.

How can we keep the fragmented usage environments that can simply encode mutual
exclusion between using the scrutinee resources (in CaseWHNF), the case
binder, or \emph{all} the pattern variables exactly once; while allowing this substitution to happen.

I think the solution is to \textbf{allow rearraging the usage environments}.
Even better, don't specify how tagged resources are distributed amongst the
usage environments, as long as all linear pat-vars are assigned at least one
resource, and that all resources are split on that constructor!

With this generalization in place, we are able to rather write the above example as
\begin{code}
f x y =
  case K x y of
    K a{x#K1,x#K2} b{y#K1, y#K2} -> (a, b)
\end{code}
for which it is now obvious we can split $x$ and $y$ and have them match the usage environment as the pattern variable they are substituting!

% (Perhaps for an implementation we need to split evenly and then rearrange before substituting? or not check the envs in the substitution)

That makes the new $AltN$ rule
\[
\TypeAltN
\]
where $\ov{\D_i}$ is any (non-empty) combination of $K$-fragmented resources
from $\D_s$.

This almost works, were it not for the fact we might want to substitute
the pattern variable by an expression that doesn't use resources, despite the
pattern-variable being linear.

In the case alternative, we must treat all linear variables equally in a way
that ensures if one of them is used then all of them are used exactly once.
Splitting resources equally amongst the variable works, but requires
rearranging s.t. the substitution environment matches the variable environment.
By allowing the var environment to be any (non-empty) arrangement a-priori we
facilitate the substitution.

Regarding the arragement being necessarily non-empty: perhaps when substituting
we can identify these variables and say something special about them in the
proof, like what? Perhaps the posterior rearrangement really is the best idea?

