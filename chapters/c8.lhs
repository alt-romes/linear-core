%include polycode.fmt
%format ⊸ = "\lolli"
\chapter{Conclusion\label{sec:discussion}}

Linear Core is an intermediate language with a type system system that
understands (semantic) linearity in the presence of laziness, suitable for
optimising compilers with these characteristics which leverage laziness and
(possibly) linearity in its transformations.

In this chapter, review the literature related to our own work, highlighting
Linear Core's novel contributions in light of the existing prominent works in
the area, or how they otherwise compare,
% (including linearity in a lazy, evaluation models in terms of linearity, and
% the Core system).
%
consider further research deemed out of the scope of our work and of the Linear
Core type system (notably, we discuss so-called \emph{multiplicity coercions}
to handle the interaction between linearity and coercions, a key feature of
Core which we left out our system), and conclude.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Related Work
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Related Work}

In this section we discuss related work, namely, Linear
Haskell~\cite{cite:linearhaskell}, Linear Mini-Core~\cite{cite:minicore}, and
linearity-influenced optimising
transformations~\cite{cite:let-floating,peytonjones1997a,cite:linearhaskell}.

% TODO: A brief introduction to the related work section?

% \subsection{Formalization of Core}\todo{terrible paragraph name, and terrible paragraph}
% 
% As such, there exists no formal definition of Core that
% accounts for linearity. In this context, we intend to introduce a linearly typed
% System $F_C$ with multiplicity annotations and typing rules to serve
% as a basis for a linear Core. Critically, this Core linear language
% must account for call-by-need evaluation semantics and be valid in
% light of Core-to-Core optimising transformations.

% \parawith{System FC}

%System $F_C$~\cite{cite:systemfc} (Section~\ref{sec:core}) does not
%account for linearity in its original design, and, to the best of our
%knowledge, no extension to System $F_C$ with linearity and non-strict
%semantics exists.
%

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

% \todo[inline]{Say something about Linear Haskell's lazy operational semantics,
% but the type system not being concerned with linearity in the presence of
% laziness}

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
annotations. Core's type system is unable to type \emph{semantic} linearity of
programs (in contrast to \emph{syntactic} linearity), which result in Core
rejecting linear programs resulting from optimising transformations that
leverage the non-strict semantics of Core.
%
Linear Core overcomes the limitations of Core's linear type system derived from
Linear Haskell by understanding semantic linearity in the presence of laziness,
and provably accepts multiple Core-to-Core passes. Linear Core, ultimately, can
also be seen as a system that validates the programs written in Linear Haskell
and compiled by GHC by guaranteeing (through typing) that linear resources are
still used exactly once throughout the optimising transformations.

\subsection{Linear Mini-Core\label{sec:linear-mini-core}}

Linear Mini-Core~\cite{cite:minicore} is a specification of linear types in
Core as they were being implemented in GHC, and doubles as the (unpublished)
precursor to our work. Linear Mini-Core first observes the incapacity of
Core's type system to accept linear programs after transformations, and first
introduces usage environments for let-bound variables with the same goal of
Linear Core of specifying a linear type system for Core that accepts the
optimising transformations.

We draw from Linear Mini-Core's the rule for non-recursive let
expressions and how let-bound variables are annotated with a usage environment,
however, our work further explores the interaction of laziness with linearity
in depth, and diverges in rules for typing other constructs, notably, case
expressions and case alternatives. Furthermore, we prove soundness of our
system and that multiple optimising transformations, when applied to Linear
Core programs, preserve linearity as understood by the system.

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

By fully supporting linear types in Core, these optimising transformations
could be informed by the language inherent linearity, and, consequently, avoid
an ad-hoc or incomplete linear-type inference pass custom-built for
optimizations. Additionally, the linearity information may potentially be used
to the benefit of optimising transformations that currently don't take any
linearity into account.

% \begin{itemize}
% \item Transfs. core to core aparecem em vários artigos, e são desenhadas no contexto de uma linguagem tipificada mas que não é linearly typed.
% \item nestes dois artigos é observado que se houvesse a capacidade de explorar linearidade podiamos fazer as coisas de forma diferente
% \item Todas estas optimizaçoes de decadas foram desenhadas sem linear types e há sitios onde linear types podiam ajudar mas não existiam na altura
% \item POdemos usar linear types multiplicitpiadads para lazy language core q definimos para nao ter de fazer sistemas lineares de proposito para optimizações
% \item Ser ad-hoc incompleto ou nao feito de todo
% \end{itemize}

% \parawith{A transformation based optimiser for Haskell}
% They discuss a cardinality analysis based on a linear type system but create (an
% ad-hoc?) one suited. Comparison in the measure of creating optimizations based
% on linearity.
% 
% \parawith{Let-Floating: Moving Bindings to Give Faster Programs\label{sec:rw:let-floating}}
% In the paper~\cite{cite:let-floating}...
% They say they are doing work on a linear type system to identify places where
% the lambda is linearly used and therefore floating-in is beneficial and
% floating-out not as productive.

% \subsection{Call-by-value, call-by-name and call-by-value...}
% 
% The work~\cite{cite:call-by-name-value-and-need-linear-lambda-calculus}...

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Future Work
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
\section{Future Work\label{sec:future-work}}

In this section we highlight some avenues of further research. Briefly,
these include \emph{multiplicity coercions}, optimisations leveraging
linearity, resource inference for usage environments, and ultimately using
Linear Core in a mature optimising compiler with lazy evaluation and linear
types -- the Glasgow Haskell Compiler. Lastly, we discuss the
% we hypothesize Linear($X$), a linear system parametrized on the evaluation strategy, and the
generalization of Linear Core to the surface Haskell language.

\parawith{Multiplicity Coercions.}
Linear Core doesn't have type equality coercions, a flagship feature of GHC
Core's type system.
%
Coercions, briefly explained in Section~\ref{sec:core},
allow the Core intermediate language to encode a panoply of Haskell source
type-level features such as GADTs, type families or newtypes.
%
In Linear Haskell, multiplicities are introduced as annotations to function
arrows which specify the linearity of the function. In practice,
multiplicities are simply types of kind |Multiplicity|, where |One| and |Many|
are the type constructors of the kind |Multiplicity|; multiplicity polymorphism
follows from (any kind) type polymorphism, where multiplicity variables are
just type variables. Encoding multiplicities as types allows Haskell programs
to leverage features available for types to naturally extend to multiplicities
as well.
%
Consequently, we might define, e.g., using a GADT |SBool| and a type family
|If|, the function |dep| which is linear in the second argument if the first
argument is |STrue| and unrestricted otherwise:
%
\begin{limitation}
\begin{code}
data SBool :: Bool -> Type where
  STrue :: SBool True
  SFalse :: SBool False

type family If b t f where
  If True t _ = t
  If False _ f = f

dep :: SBool b -> Int %(If b One Many) -> Int
dep STrue x = x
dep SFalse _ = 0
\end{code}
\end{limitation}
%
In theory, this example is linear and should be accepted. However, in practice,
the example is rejected by the GHC's Core type checker. Critically, Core doesn't
currently understand so-called \emph{multiplicity coercions}. Even though after
matching on |STrue| we have access to a coercion from the function multiplicity
$m$ to $1$ ($m \sim 1$), we cannot use this coercion to determine whether the
usages of the linear resources match the multiplicity.
%
Studying the interaction between coercions and multiplicities is a main avenue
of future work for Linear Core.

% In GHC, multiplicity coercions are tracked by issue $19517$\footnote{https://gitlab.haskell.org/ghc/ghc/-/issues/19517}.

% \todo[inline]{Relate to levity polymorphism and runtime rep coercions (Sam)}

\parawith{Optimisations leveraging linearity.}
We only briefly mentioned how linearity can inform optimisations to produce
more performant programs. We leave exploring optimisations unblocked by
preserving linearity in the intermediate language with Linear Core as future
work. Linearity influenced optimising transformations have been also discussed
by Linear Haskell~\cite{cite:linearhaskell} and
in~\cite{cite:let-floating,peytonjones1997a}. An obvious candidate is
\emph{inlining}, which is applied based on heuristics from information provided
by the \emph{cardinality analysis} pass that counts occurrences of bound
variables.  Linearity, in being user-provided annotations regarding the usage
of resources in the body of a function, can be used to inform non-heuristically
the inliner~\cite{cite:linearhaskell}. Additionally, we argue that in Linear
Core accepting more programs as linear there are more chances to (ab)use
linearity, in contrast to a linear type system which does not account for lazy
evaluation and thus rejects more programs.

\parawith{Usage environment resource inference.}
In Section~\ref{sec:linearity-semantically}, we explained that the linear
resources used by a group of recursive bindings aren't obvious and must be
consistent with each other (i.e. considering the mutually-recursive calls) as
though the resources used by each binder are the solution to a set determined
by the recursive bindings group.  In Section~\ref{sec:main:linear-core}, we
further likened the challenge of determining usage environments for a recursive
group of bindings to a unification problem as that solved by the Hindley-Milner
type inference algorithm~\cite{10.1145/582153.582176} based on generating and solving
constraints. Even though these are useful observations, our implementation of
Linear Core uses a naive algorithm to determine the usage environments, thereby
leaving as future work the design of a principled algorithm to determine the
usage environments of recursive group of bindings.

\parawith{Linear Core in the Glasgow Haskell Compiler.}
Linear Core is suitable as the intermediate language of an optimising compiler
for a linear and lazy language such as Haskell Core, in that optimising
transformations in Linear Core preserve types \emph{and} linearity since Linear
Core understands (semantic) in the presence of laziness, unlike Core's current
type system under which optimisations currently violate linearity.
%
Integrating Linear Core in the Glasgow Haskell Compiler is one of the ultimate
goals motivating our work. Core's current type system ignores linearity due to
its limitation in understanding semantic linearity, and our work fills this gap
and would allow Core to be linearly typed all throughout.
%
A linearly typed Core that preserves linearity throughout the optimisation
pipeline of GHC both validates the correctness of the compiler, which is
already achieved to a great extent by preserving (non-linear) types, and
informs optimisations, allowing the compiler to generate more performant programs.

Implementing Linear Core in GHC is a challenging endeavour, since we must account
for all other Core features (e.g. strict constructor fields) and more
optimisations. Despite our initiative in this
direction\footnote{https://gitlab.haskell.org/ghc/ghc/-/issues/23218}, we leave
this as future work.

\parawith{Generalizing Linear Core to Haskell.}
Linear types, despite its compile-time correctness guarantees regarding
resource management, impose a burden on programmers in being a restrictive
typing discipline (witnessed, e.g., by Linear
Constraints~\cite{cite:linearconstraints}). Linear Core eases the restrictions
of linear typing by being more flexible in understanding linearity for lazily
evaluated languages such as Haskell. In this sense, it is an avenue of future
work to apply the ideas from Linear Core to the surface Haskell language.

% \begin{itemize}
% 
% \item Linear(X), a linear type system defined by the underlying definition of
% evaluation (which in turn implies how consuming a resource is defined)
% 
% \item Implementation in Core
% 
% \item Generalization to source level language, being more permissive in the
% handling of resources imposes less burden on the programmer
% 
% \item It's harder to typecheck linearity like this in the source level because
% of the interaction with other source features, but seems feasible and an
% improvement to the usability of linear types. It allows more lazy functional
% programming idioms with linear types (also because laziness and strictness is less well defined as in Core, bc opts)
% 
% \item Beautiful inference algorithm for recursive usage environments -- insight
% that looks like inference for recursive function principle types, but haven't
% figured it out -- connection to type inference / hindley milner
% 
% \item We kind of ignore the multiplicity semiring. We should discuss
% how we don't do ring operations ... but that's kind of wrong.
% 
% % \item We know the case binder to ALWAYS be in WHNF, perhaps there could
% % be some annotation on the case binder s.t. we know nothing happens when we
% % scrutinize it as a single variable
% 
% \item Mechanizing the system and metatheory
% 
% \end{itemize}


% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% {{{ Conclusion
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% We give up on this section and instead describe "syntax-directedness" in the implementation chapter
%
%
% \section{Syntax Directed System}
% 
% \todo[inline]{In the other system we assume that the recursive lets are strongly connected, i.e. the expressions always}
% 
% \input{language-v4/SyntaxDirectedSystem}
% 
% \subsection{Inferring usage environments}
% 
% \todo[inline]{The difference between this and the previous section is a bit blurry}
% 
% \todo[inline]{There's one more concern: usage environments aren't readily
% available, especially in recursive lets. We must perform inference of usage
% environments before we can typecheck using them. This is how:}
% 
% \todo[inline]{Rather, we define a syntax directed type system that infers usage environments while checking...}
% 

\section{Conclusion}

Optimising compilers with a typed and lazy intermediate language with linear
types (of which GHC is the prime example) leverage laziness to heavily
transform and rewrite programs into simpler forms.
%
However, these optimising transformations push the interaction between
linearity and laziness to the limits where linearity can no longer be seen
syntactically, despite being maintained semantically, in the sense that linear
resources are still used exactly once when the optimised program is run.

In this work we explored linearity in the presence of laziness by example
through the interactions of linear types with lazy (recursive) let bindings and
case expressions that evaluate their scrutinee to Weak Head Normal. Most
example programs were linear semantically, but not syntactically.
%
We developed a linear type system, Linear Core, for an intermediate language
akin to GHC Core, with laziness and linearity. In contrast to GHC Core's type
system, or any other linear type system (to the best of our knowledge), our
type system understands semantic linearity, and (anecdotally) accepts as
well-typed all but one of the programs explored in the semantic linearity
examples.
%
Crucially, we proved soundness of the type system, and proved multiple
optimising transformations preserve linearity, despite most violating linearity
in other linear type systems. Additionally, we implemented Linear Core as a GHC
plugin to further explore its suitability in the intermediate language of an
optimising compiler.

Concluding, Linear Core is a suitable type system for linear, lazy,
intermediate languages of optimising compilers such as GHC, as it understands
linearity in the presence of laziness s.t. optimisations preserve types and
linearity, and further unblocks optimisations influenced by linearity, e.g.
inlining and call-by-name $\beta$-reduction for applications of (semantically)
linear functions.

% }}}
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% vim: fen fdm=marker
