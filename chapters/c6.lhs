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
