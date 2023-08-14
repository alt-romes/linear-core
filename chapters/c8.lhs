\chapter{Discussion}

\todo[inline]{Preamble}

\section{Related Work}

% TODO: A brief introduction to the related work section?

\parawith{Formalization of Core}\todo{terrible paragraph name}

System $F_C$~\cite{cite:systemfc} (Section~\ref{sec:core}) does not
account for linearity in its original design, and, to the best of our
knowledge, no extension to System $F_C$ with linearity and non-strict
semantics exists.
%
As such, there exists no formal definition of Core that
accounts for linearity. In this context, we intend to introduce a linearly typed
System $F_C$ with multiplicity annotations and typing rules to serve
as a basis for a linear Core. Critically, this Core linear language
must account for call-by-need evaluation semantics and be valid in
light of Core-to-Core optimizing transformations.

% \parawith{System FC}

% \begin{itemize}
% \item SystemFC tal como está não tem linearidade de todo
% \item Formalmente nao temos published definição de linearidade no Core
% \item Regras para sistema tipo FC com linearidade
% \item mas uma extensão tipo linear lambda calculus nao consegui exprimir as transformações do core
% \end{itemize}

% Haskell Core's foundational language was imbued with linear types, but it does
% not account for linearity with the whole of the type system
% 
% Multiplicity annotations in SystemFC?
% 
% Rules?

\parawith{Linear Haskell\label{sec:related-work-linear-haskell}}

Haskell, contrary to most programming languages with linear types, has existed
for 31 years of its life \emph{without} linear types. As such, the introduction
of linear types to Haskell comes with added challenges that do not exist in
languages that were designed with linear types from the start:
%
\begin{itemize}
    \item Backwards compatibility. The addition of linear types shouldn't break
        all existing Haskell code.
    \item Code re-usability. The linearly-typed part of Haskell's ecosystem and
        its non-linearly-typed counterpart should fit in together and it must be
        possible to define functions readily usable by both sides
        simultaneously.
    \item Future-proofing. Haskell, despite being an
        industrial-strength language, is also a petri-dish for experimentation
        and innovation in the field of programming languages. Therefore, Linear
        Haskell takes care to accomodate possible future features, in
        particular, its design is forwards compatible with affine and dependent
        types.
\end{itemize}
%
Linear Haskell~\cite{cite:linearhaskell} is thus concerned with retrofitting
linear types in Haskell, taking into consideration the above design goals, but
is not concerned with extending Haskell's intermediate language(s),
which presents its own challenges. 

Nonetheless, while the Linear Haskell work keeps Core unchanged, its
implementation in GHC does modify and extend Core with linearity/multiplicity
annotations, and said extension of Core with linear types does not account for
optimizing transformations and the non-strict semantics of Core.

Our work on linear Core intends to overcome the limitations of linear types as
they exist in Core, i.e. integrating call-by-need semantics and validating the
Core-to-Core passes, ultimately doubling as a validation of the implementation
of Linear Haskell.


% \subsection{OutsideIn(X)\label{related-work-gadts}}
% 
% Defines constraint-based type system parametrized over X which does not account
% for local type refinements regarding linearity.
% 
% Se for modificar o typechecker com as multiplicity coercions vou ter de falar
% disto.

% \subsection{Rust}
% 
% Rust has a core based on linear types. Describe Rust's architecture?
% How do they handle linearity plus optimizations
% They probabluy don't typecheck linearity in Core

\parawith{Linearity-influenced optimizations}

Core-to-Core transformations appear in many works across the research
literature~\cite{cite:let-floating,peytonjones1997a,santos1995compilation,peytonjones2002secrets,baker-finch2004constructed,maurer2017compiling,Breitner2016_1000054251,sergey_vytiniotis_jones_breitner_2017},
all designed in the context of a typed language (Core) which does not have
linear types. However,
~\cite{cite:let-floating,peytonjones1997a,cite:linearhaskell} observe that
certain optimizations (in particular, let-floating and inlining) greatly
benefit from linearity analysis and, in order to improve those transformation,
linear-type-inspired systems were created specifically for the purpose of the
transformation.

By fully supporting linear types in Core, these optimizing transformations
could be informed by the language inherent linearity, and, consequently, avoid
an ad-hoc or incomplete linear-type inference pass custom-built for
optimizations. Additionally, the linearity information may potentially be used
to the benefit of optimizing transformations that currently don't take any
linearity into account.

% \begin{itemize}
% \item Transfs. core to core aparecem em vários artigos, e são desenhadas no contexto de uma linguagem tipificada mas que não é linearly typed.
% \item nestes dois artigos é observado que se houvesse a capacidade de explorar linearidade podiamos fazer as coisas de forma diferente
% \item Todas estas optimizaçoes de decadas foram desenhadas sem linear types e há sitios onde linear types podiam ajudar mas não existiam na altura
% \item POdemos usar linear types multiplicitpiadads para lazy language core q definimos para nao ter de fazer sistemas lineares de proposito para optimizações
% \item Ser ad-hoc incompleto ou nao feito de todo
% \end{itemize}

% \parawith{A transformation based optimizer for Haskell}
% They discuss a cardinality analysis based on a linear type system but create (an
% ad-hoc?) one suited. Comparison in the measure of creating optimizations based
% on linearity.
% 
% \parawith{Let-Floating: Moving Bindings to Give Faster Programs\label{sec:rw:let-floating}}
% In the paper~\cite{cite:let-floating}...
% They say they are doing work on a linear type system to identify places where
% the lambda is linearly used and therefore floating-in is beneficial and
% floating-out not as productive.

\section{Future Work}

\section{Conclusions}


