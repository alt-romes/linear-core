%include polycode.fmt
%format ⊸ = "\lolli"
\chapter{Discussion}

Preamble

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Chapter: Linear Core as a GHC Plugin; Introduction
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

\section{Linear Core as a GHC Plugin}

This section discusses the implementation of Linear Core as a GHC Plugin, with
a dash of painful history in the attempt of implementing Linear Core directly
into GHC.

Discuss a bit syntax-directedness non existent in the system and that our implementation slightly tweaks it to be more syntax directed or something

Talk about using our plugin on linear-base and other code bases... If I can get
a few more case studies it would be pretty good. But then it's imperative to
also use -dlinear-lint and make sure my plugin rejects a few of the examples

% Introduction...

\subsection{Consuming tagged resources as needed}

As discussed in Section~\ref{}, constructor pattern bound linear variables are
put in the context with a \emph{tagged} usage environment with the resources of
the scrutinee. In a \emph{tagged} usage environment environment, all resources
are tagged with a constructor and an index into the many fields of the
constructor.

In practice, a resource might have more than one tag. For example, in the following
program, after the first pattern match, |a| and |b| have, respectively, usage
environments $\{\lctag{x}{K_1}\}$ and $\{\lctag{x}{K_2}\}$:
\begin{code}
f x = case x of
       K a b -> case a of
        Pair n p -> (n,p)
\end{code}
However, in the following alternative, |n| has usage environment
$\{\lctag{\lctag{x}{K_1}}{Pair_1}\}$ and |p| has
$\{\lctag{\lctag{x}{K_1}}{Pair_2}\}$. To typecheck
|(n,p)|, one has to $Split$ |x| first on |K| and then on |Pair|, in order for
the usage environments to match.

In our implementation, we split resources on demand (and don't directly allow
splitting linear resources), i.e. when we use a tagged resource we split the
linear resource in the linear environment (if available), but never split otherwise.
%
Namely, starting on the innermost tag (the closest to the variable name), we
substitute the linear resource for its split fragments, and then we iteratively
further split those fragments if there are additional tags.
%
We note that it is safe to destructively split the resource (i.e. removing the
original and only leaving the split fragments) because we only split resources
when we need to consume a fragment, and as soon as one fragment is consumed
then using the original ``whole'' variable would violate linearity.

In the example, if |n| is used, we have to use its usage environment, which in
turn entails using $\lctag{\lctag{x}{K_1}}{Pair_1}$, which has two tags. In this order, we:
\begin{itemize}
\item Split $x$ into $\lctag{x}{K_1}$ and $\lctag{x}{K_2}$
\item Split $\lctag{x}{K_1}$ and $\lctag{x}{K_2}$ into
  \begin{itemize}
  \item $\lctag{\lctag{x}{K_1}}{Pair_1}$ and $\lctag{\lctag{x}{K_1}}{Pair_2}$
  \item Leave $\lctag{x}{K_2}$ untouched, as we only split on demand, and we aren't using a fragment of $\lctag{x}{K_2}$.
  \end{itemize}
\item Consume $\lctag{\lctag{x}{K_1}}{Pair_1}$, the usage environment of $n$, by removing it from the typing environment.
\end{itemize}


% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Related Work
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related Work}

% TODO: A brief introduction to the related work section?

\subsection{Formalization of Core}\todo{terrible paragraph name, and terrible paragraph}

%System $F_C$~\cite{cite:systemfc} (Section~\ref{sec:core}) does not
%account for linearity in its original design, and, to the best of our
%knowledge, no extension to System $F_C$ with linearity and non-strict
%semantics exists.
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

\subsection{Linear Haskell\label{sec:related-work-linear-haskell}}

\todo[inline]{Say something about Linear Haskell's lazy operational semantics,
but the type system not being concerned with linearity in the presence of
laziness}

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
        Haskell takes care to accommodate possible future features, in
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

\subsection{Linear Mini-Core\label{sec:linear-mini-core}}

Linear Mini core is the precursor to our work

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

\subsection{Linearity-influenced optimizations}

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

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Future Work
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Future Work\label{sec:future-work}}

\begin{itemize}
\item Linear(X), a linear type system defined by the underlying definition of evaluation (which in turn implies how consuming a resource is defined)
\item Implementation in Core
\item Generalization to source level language, being more permissive in the
handling of resources imposes less burden on the programmer
\item It's harder to typecheck linearity like this in the source level because
of the interaction with other source features, but seems feasible and an
improvement to the usability of linear types. It allows more lazy functional
programming idioms with linear types (also because laziness and strictness is less well defined as in Core, bc opts)

\item Beautiful inference algorithm for recursive usage environments -- insight
that looks like inference for recursive function principle types, but haven't
figured it out

\item Beautiful inference of usage environments - connection to type inference / hindley milner

\item We kind of ignore the multiplicity semiring. We should discuss
how we don't do ring operations ... but that's kind of wrong.

\item We know the case binder to ALWAYS be in WHNF, perhaps there could
be some annotation on the case binder s.t. we know nothing happens when we
scrutinize it as a single variable

\item Should we discuss this? It would be fine, but we're not able to see this because of call-by-name substitution. I say yes, in the reverse binder swap section
\begin{code}
f x = case x of z { _ -> x }
\end{code}

\end{itemize}

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Conclusions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Conclusions}

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% vim: fen fdm=marker
