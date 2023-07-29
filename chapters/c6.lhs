%include polycode.fmt
\chapter{Linear Core, again}

% Proof macros
\input{language-v2/proof}

\input{language-v2/Syntax}

\clearpage
\input{language-v2/TypingRules}

\chapter{Linear Core, again, again}

% Proof macros for v3
\input{language-v3/proof}

\input{language-v3/Syntax}

\input{language-v3/TypingRules}

\input{language-v3/OperationalSemantics}

%\clearpage
% \section{Type Safety}

% \input{language-v3/proofs/TypePreservationTheorem}

% \input{language-v3/proofs/ProgressTheorem}

% \input{language-v3/proofs/LinearSubstitutionLemma}

% \input{language-v3/proofs/UnrestrictedSubstitutionLemma}
% 
% \input{language-v3/proofs/DeltaSubstitutionLemma}
% 
\clearpage

TODO! Substitution of proof-irrelevant linear variables preserves typing. The
term always remains the same because $x$ cannot occur in any term, however, all
variables that refer to $x$ in their usage environment must now refer the usage env. of the substitee (e.g. $[x] => [\D]$).
This seems trivial to see correct, since all occurrences are in environments, so we get some equivalence similar to the one we need for the proof of Alt0.

\begin{lemma}[Substitution of proof-irrelevant linear variables preserves typing]
If $\judg[\G][\D,\irr{\x}][\d]{e}{\vp}$ and $\judg[\G][\D'][\d']{e'}{\s}$ then $\judg[\G][\D,\irr{\D'}][\subst{\d}{\D'}{x},\d']{e}{\vp}$
\end{lemma}

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

