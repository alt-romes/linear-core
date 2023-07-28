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

\clearpage
\section{Type Safety}

\input{language-v3/proofs/TypePreservationTheorem}

\input{language-v3/proofs/ProgressTheorem}

\input{language-v3/proofs/LinearSubstitutionLemma}

\input{language-v3/proofs/UnrestrictedSubstitutionLemma}

\input{language-v3/proofs/DeltaSubstitutionLemma}

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

% \input{language-v3/InferUsageEnvs}

\input{language-v3/proofs/optimizations/Inlining}
\input{language-v3/proofs/optimizations/BetaReduction}
\input{language-v3/proofs/optimizations/CaseOfKnownConstructor}
\input{language-v3/proofs/optimizations/LetFloating}
\input{language-v3/proofs/optimizations/CaseOfCase}
\input{language-v3/proofs/optimizations/BinderSwap}
