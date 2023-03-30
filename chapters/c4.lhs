%include polycode.fmt
\input{proof}
\renewcommand{\llet}[2]{\mathbf{let}~#1~\mathbf{in}~#2}
\renewcommand{\lletrec}[2]{\mathbf{let~rec}~#1~\mathbf{in}~#2}
\renewcommand{\ccase}[2]{\mathbf{case}~#1~\mathbf{of}~#2}
\newcommand{\judgment}[1]{
    \begin{tabular}{V{2.7}cV{2.7}}
    \hlineB{2.7}
    $#1$\\
    \hlineB{2.7}
    \end{tabular}
}
\newcommand{\datatype}[2]{
  \mathbf{data}~#1~\mathbf{where}~#2
}

\chapter{Linear Core*}

\input{language/Syntax}

\clearpage
\input{language/TypingRules}

\clearpage
\input{language/OperationalSemantics}

\clearpage
\input{language/InferUsageEnvs}

\clearpage
\section{Type Soundness}

\input{language/proofs/TypePreservationTheorem}

\clearpage
\input{language/proofs/ProgressTheorem}

\clearpage
\input{language/proofs/LinearSubstitutionLemma}

\clearpage
\input{language/proofs/UnrestrictedSubstitutionLemma}

\clearpage
\input{language/proofs/DeltaSubstitutionLemma}

