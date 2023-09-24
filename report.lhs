\documentclass{lwnovathesis}
\usepackage{mathtools}
\usepackage{boldline}
\usepackage{xargs}
\usepackage{soul}
\usepackage[colorinlistoftodos=true]{todonotes}
\usepackage{cmll}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{amsthm}
\usepackage{mathpartir}
\usepackage[ruled,vlined]{algorithm2e}
\usepackage{fancyvrb}
\usepackage{cleveref}
\usepackage{tikz}
\usepackage{tikz-qtree}
\usetikzlibrary{trees}	% this is to allow the fork right path
\usepackage{mdframed}

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}%[theorem]
\newtheorem{sublemma}{Lemma}[lemma]
\newtheorem{assumption}{Assumption}

% Glossary
\usepackage[toc]{glossaries}

%%%%%%%%%%%%%%  Color-related things   %%%%%%%%%%%%%%

%include polycode.fmt
%format ⊸ = "\lolli"
%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"

\newcommand{\myFor}[2]{\For{$#1$}{$#2$}}
\newcommand{\id}[1]{\textsf{\textsl{#1}}}

\renewcommand{\Varid}[1]{\textcolor{Sepia}{\id{#1}}}
\renewcommand{\Conid}[1]{\textcolor{OliveGreen}{\id{#1}}}

%%%%%%%%%%%%  End of Color-related things   %%%%%%%%%%%%

% It might make sence to add pretty formating of individual things
% like "forall", cf.
% https://github.com/goldfirere/thesis/blob/master/tex/rae.fmt

% colorboxes, from rae's thesis as well
\definecolor{notyet}{rgb}{1,1,0.85}
\newmdenv[hidealllines=true,backgroundcolor=notyet,innerleftmargin=0pt,innerrightmargin=0pt,innertopmargin=-3pt,innerbottommargin=-3pt,skipabove=3pt,skipbelow=3pt]{notyet}
\newcommand{\notyetcolorname}{light yellow}

\definecolor{working}{rgb}{0.9,1,0.9}
\newmdenv[hidealllines=true,backgroundcolor=working,innerleftmargin=0pt,innerrightmargin=0pt,innertopmargin=-3pt,innerbottommargin=-3pt,skipabove=3pt,skipbelow=3pt]{working}
\newcommand{\workingcolorname}{light green}

\definecolor{noway}{rgb}{1,0.9,0.9}
\newmdenv[hidealllines=true,backgroundcolor=noway,innerleftmargin=0pt,innerrightmargin=0pt,innertopmargin=-3pt,innerbottommargin=-3pt,skipabove=3pt,skipbelow=3pt]{noway}
\newcommand{\nowaycolorname}{light red}

\DefineVerbatimEnvironment{code}{Verbatim}{fontsize=\small}
\DefineVerbatimEnvironment{example}{Verbatim}{fontsize=\small}

\newcommand{\parawith}[1]{\paragraph{\emph{#1}}}
\newcommand{\lolli}{\multimap}
\newcommand{\tensor}{\otimes}
\newcommand{\one}{\mathbf{1}}
\newcommand{\bang}{{!}}

\newcommand{\llet}[2]{\mathsf{let}~#1~\mathsf{in}~#2}
\newcommand{\lletrec}[2]{\mathsf{letrec}~#1~\mathsf{in}~#2}
\newcommand{\ccase}[2]{\mathsf{case}~#1~\mathsf{of}~#2}

\title{Type-checking Linearity in Core\\ or: Semantic Linearity for a Lazy Optimising Compiler}
\author{Rodrigo Mesquita \\ Bernardo Toninho}


\makeglossaries

\newglossaryentry{GHC}
{
    name=GHC,
    description={The Glorious Glasgow Haskell Compiler}
}

\newglossaryentry{GADT}
{
    name=GADT,
    description={Generalized Algebraic Data Types}
}

\begin{document}

%%%%%%%%%%%%%% TODOs %%%%%%%%%%%%%
\listoftodos

\todostyle{blue}{color=blue}   % For todos without a home
\todostyle{pink}{color=pink} % For foreshadowing things, or for saying them later on instead
\todo[blue, inline]{We need to handle EmptyCase}
\todo[blue, inline]{And discuss how we didn't handle multiplicity coercions}
\todo[blue, inline]{Consider dropping some bits about GADTs?}
\todo[inline, inline]{Symbol to stand for both $1$ and $p$, and notation to make proof
irrelevant stuff in the types so we can also refer to relevant and irrelevant
at the same time with some symbol (e.g. for Split)}

%%%%%%%%%% End TODOs %%%%%%%%%%%%%

\frontmatter

\maketitle
\cleardoublepage

\abstractnum
\begin{abstract}
Linear types were added both to Haskell and to its Core intermediate language,
which is used as an internal consistency tool to validate the transformations a
Haskell program undergoes during compilation.
%
However, the current Core type-checker rejects many linearly valid programs
that originate from Core-to-Core optimising transformations. As such, linearity
typing is effectively disabled, for otherwise disabling optimizations would be
far more devastating.
%
% This dissertation presents an extension to Core's type system that accepts a
The goal of our proposed dissertation is to develop an extension to Core's type
system that accepts a larger amount of programs and verifies that optimising
transformations applied to well-typed linear Core produce well-typed linear
Core.
%
Our extension will be based on attaching variable \emph{usage environments} to
binders, which augment the type system with more  fine-grained contextual
linearity information, allowing the system to accept programs which seem to
syntactically violate linearity but preserve linear resource usage. We will
also develop a usage environment inference procedure and integrate the
procedure with the type checker.  We will validate our proposal by showing a
range of Core-to-Core transformations can be typed by our system.
\end{abstract}
\cleardoublepage

\renewcommand{\abstractname}{Resumo}
\begin{abstract}
Tipos lineares foram integrados ambos no Haskell e na sua linguagem intermédia,
Core, que serve como uma ferramenta de consistência interna do compilador que
valida as transformações feitas nos programas ao longo do processo de
compilação.
%
No entanto, o sistema de tipos do Core rejeita programas lineares válidos que
são produto de optimizações Core-to-Core, de tal forma que a validação da
linearidade ao nível do sistema de tipos não consegue ser desempenhada com
sucesso, sendo que a alternativa, não aplicar optimizações, tem resultados
bastante mais indesejáveis.
%
O objetivo da dissertação que nos propomos a fazer é extender ao sistema de
tipos do Core de forma a aceitar mais programas lineares, e verificar que as
optimizações usadas não destroem a linearidade dos programas.
%
A nossa extensão parte de adicionar \emph{ambientes de uso} às variáveis,
aumentando o sistema de tipos com informação de linearidade suficiente para
aceitar programas que aparentemente violam linearidade sintaticamente, mas que
a preservam a um nível semântico. Para além do sistema de tipos, vamos
desenvolver um algoritmo de inferência de \emph{ambientes de uso}. Vamos
validar a nossa proposta através do conjunto de transformações Core-to-Core que
o nosso sistema consegue tipificar.
\end{abstract}
\cleardoublepage

\xtableofcontents
\xlistoffigures
% \xlistoftables
% \printglossaries

\mainmatter

% \OnehalfSpacing

% TODO: linear functions to allow safe/controlled use of reified language
% implementation objects like *single-use continuations* (single use
% continuations? can we make them faster?)

\chapter{Introduction}

% Statically typed languages 
% Linear types are cool
% Among the few, Haskell has linear types
% But Haskell differs from other languages with linear types
%   * added 31 years after inception
%   * added to its core
% Core has linear types for good reasons
% But they are broken -- why?
%   * Optimizations changes source -- e.g. if recursive lets are introduced, how to type linearity?
% Goals - O que eu vou fazer
% Document Structure (pode-se eventualmente combinar com a seccao dos goals)


%\section{Introduction}

Statically safe programming languages provide compile time correctness
guarantees by having the compiler rule out certain classes of errors
or invalid programs. Moreover, static typing
allows programmers to state and enforce (compile-time) invariants
relevant to their problem domain.
In this sense, type safety entails that all
possible executions of a type-correct program cannot exhibit behaviors
deemed ``wrong'' by the type system design. This idea is captured in
the motto ``well-typed programs do not go wrong''.%~\cite{}.


Linear type systems~\cite{cite:linear-logic,cite:barberdill} add expressiveness
to existing type systems by enforcing that certain \emph{resources} (e.g.~a
file handle) must be used \emph{exactly once}.
%
In programming languages with a linear type system, not using certain resources
or using them twice are flagged as type errors. Linear types can thus be used
to, e.g., statically guarantee that socket descriptors or heap-allocated memory
is freed exactly once (leaks and double-frees become type
errors), or guarantee channel-based communication protocols are
deadlock-free~\cite{10.1007/978-3-642-15375-4_16},
% implement safe
% high-performance language interoperability~\cite{}, 
%guarantee that quantum entangled states are not duplicated~\cite{}
among other high-level correctness properties~\cite{10.1145/3373718.3394765,10.1145/3527313,cite:linearhaskell}.
% handle mutable state safely~\cite{}

% TODO: Chegar mais rápido ao que vou fazer? Aqui?

As an example, consider the following C-like program in which allocated memory
is freed twice. We know this to be the dreaded double-free error which will
crash the program at runtime. Regardless, a C-like type system will accept this
program without any issue:
\begin{code}
let p = malloc(4);
in free(p);
   free(p);
\end{code}

Under the lens of a linear type system, consider the variable $p$ to be a
linear resource created by the call to \texttt{malloc}. Since $p$ is linear, it
must be used \emph{exactly once}.  However, the program above uses $p$ twice,
in the two different calls to \texttt{free}. With a linear type system, the
program above \emph{does not typecheck}! In this sense, linear typing
effectively ensures the program does not compile with a double-free error.
% TODO: Do I need this:
In Section~\ref{sec:linear-types} we give a formal account of linear types and
provide additional examples.

Despite their promise and extensive presence in research
literature~\cite{Wadler1990LinearTC,CERVESATO2000133,10.1093/logcom/2.3.297},
an effective design combining linear and non-linear typing is both
challenging and necessary to bring the advantages of linear typing to
mainstream languages.
%
Consequently, few general purpose programming languages have linear
type systems. Among them are Idris~2~\cite{brady:LIPIcs.ECOOP.2021.9},
a linearly and dependently typed language based on Quantitative Type
Theory, Rust~\cite{10.1145/2692956.2663188}, a language whose
ownership types build on linear types to guarantee memory safety
without garbage collection or reference counting, and, more recently,
Haskell~\cite{cite:linearhaskell}, a pure, functional, and
\emph{lazy} general purpose programming language.
% TODO: Extend above: it's the language of our focus

% Besides Haskell's supporting linear
% types according to the said paper, Idris 2\cite{} supports linear types in a
% dependently typed setting, Clean\cite{} has uniqueness types which are closely
% related to linear types, and Rust\cite{} has ownership types which build from
% linear types. 

Linearity in Haskell stands out from linearity in Rust and Idris 2
due to the following reasons:

\begin{itemize}
    \item Linear types were only added to the language roughly \emph{31 years
        after} Haskell's inception, unlike Rust and Idris 2 which were designed
        with linearity from the start. It is an especially difficult endeavour
        to add linear types to a well-established language with a large library
        ecosystem and many active users, rather than to develop the language
        from the ground up with linear types in mind. The successful
        approach as implemented in the Glasgow Haskell Compiler (GHC), the leading
        Haskell compiler, is based on Linear Haskell~\cite{cite:linearhaskell}, which describes a linear type system designed
        with retaining backwards-compatibility and allowing code reuse across
        linear and non-linear users of the same libraries.
        We describe Linear Haskell in detail in Section~\ref{sec:linear-haskell}.

    \item Linear types permeate Haskell down to (its) Core, the
        intermediate language into which Haskell is
        translated. Core is a minimal, explicitly typed,
        functional language, to which multiple
        Core-to-Core optimising transformations are
        applied during compilation. Due to Core's minimal design, typechecking
        Core programs is very efficient and doing so serves as a sanity check to the
        correction of the source transformations. If the resulting optimised
        Core program fails to typecheck, the optimising
        transformations (are very likely to) have introduced an error
        in the resulting program. We present Core (and its formal
        basis, System~$F_C$~\cite{cite:systemfc}) in Section~\ref{sec:core}.
        % TODO: \item values in rust are linear by default while non-linear is
        % the haskell default?

    \item Both Haskell and its intermediate language Core are \emph{lazily}
        evaluated, i.e. expressions in Haskell are only evaluated when needed,
        unlike expressions in Idris or Rust that are \emph{eagerly} evaluated.
        %
        Laziness allows an optimising compiler to aggressively transform the source
        program without changing its semantics, and indeed, GHC heavily transforms
        Core by leveraging its laziness.
        %
        However, lazy evaluation interacts non-trivially with linearity. Since
        expressions are not necessarily evaluated, an occurrence of a linear
        resource in an expression does not necessarily entail consuming that
        resource (i.e. if the expression isn't evaluated, the resource isn't used).

        In eagerly evaluated languages, the distinction between syntactic uses of a
        resource and the actual use of linear resources at runtime does not exist --
        an occurrence of a variable in the program always entails consuming it.
        %
        This interaction is unique to Haskell since, as far as we know, it is the
        only language featuring both laziness and linearity.
        %
        We review lazy and eager evaluation strategies in Section~\ref{sec:background:evaluation-strategies}.

\end{itemize}
%

% Linear core good Aligned with the philosophy of having a \emph{typed}
% intermediate language, the integration of linear types in Haskell required
% extending Core with linear types.
%
Much like a typed Core ensures that the translation from Haskell (dubbed
\emph{desugaring}) and the subsequent optimising transformations applied to
Core are correctly implemented, a \emph{linearly typed} Core guarantees that
linear resource usage in the source language is not violated by the translation
process and the compiler optimization passes.
%
It is crucial that a program's behaviour enforced by linear types is \emph{not}
changed by the compiler in the desugaring or optimization stages (optimizations
should not destroy linearity!) and a linearity aware Core type-checker is key in
providing such guarantees -- it would be disastrous if the compiler, e.g.,
duplicated a pointer to heap-allocated memory that was previously just used
once and then freed in the original program.
%TODO: linearidade pode informar otimizacoes
%
Even more, linearity in Core can inform Core-to-Core optimising
transformations~\cite{cite:let-floating,peytonjones1997a,cite:linearhaskell},
such as inlining and $\beta$-reduction, to produce more performant programs.

% Linear core actually not so good
% Additionally, while not yet a reality, linearity in Core could be used to inform
% certain program optimizations, i.e. having linear types in Core could be used to
% further optimise certain programs and, therefore, benefit the runtime
% performance characteristics of our programs. For example, Linear Haskell\cite{}
% describes as future work an improvement to the inlining optimization: Inlining
% is a centerpiece program optimization primarily because of the subsequent
% optimising opportunities unlocked by inlining. However, it relies on a heuristic
% process known as \emph{cardinality analysis} to discover safe inlining
% opportunities. Unfortunately, heuristics can be volatile and fail in identifying
% crucial inlining opportunities resulting in programs that fall short of their
% performance potential. On the contrary, the linearity information could be
% integrated in the analysis and used as a (non-heuristic) cardinality
% \emph{declaration}.

% While the current version of Core is linearity-aware (i.e.,~Core has so-called
% multiplicity annotations in variable binders), its type system does not (fully)
% validate the linearity constraints in the desugared program and essentially
% fails to type-check programs resulting from several optimising transformations
% that are necessary to produce efficient object code. The reason for this latter
% point is not evidently clear:
% %
% if we can typecheck linearity in the surface level Haskell why do we fail to do
% so in Core?
%

In spite of a linearly typed Core ultimately being the desired intermediate
language for the Glasgow Haskell Compiler ever since Linear Haskell was
implemented, both in its expressiveness to completely represent a Haskell with
linear types, and due to the added sanity-checking/validations and potential to
improve optimisations,
% it is currently impossible to enable linearity checking in Core. The reason is
linearity is effectively ignored in Core. The reason is not evidently clear:
if we can typecheck linearity in the surface level Haskell why do we fail to do
so in Core?

The desugaring process from surface level Haskell to Core, and the subsequent
Core-to-Core optimising transformations, eliminate and rearrange most of the
syntactic constructs through which linearity checking is performed -- often
resulting in programs completely different from the original, especially due to
the flexibility laziness provides a compiler in the optimisations it may
perform without changing the program semantics.
%
Crucially, the resulting program is still linear, since optimisations don't
destroy linearity, however, the linear type system doesn't accept the resulting
programs as linear. The optimisations transform programs that are linear into
ones that don't \emph{look} linear, but remain linear \emph{semantically}. For
example, the following program, despite not looking linear (as there are two
syntactic occurrences of the linear resource $x$), \emph{is} linear, as the let
bound expression using $x$ is never evaluated (because is not needed) -- thus
$x$ is only consumed once when returned in the let body:
\begin{code}
f :: a ⊸ a
f x = let y = use x in x
\end{code}

The Core optimising transformations expose a fundamental limitation of Core's
current linear type system -- it does not account for Core's call-by-need
evaluation model, and thus a whole class of programs that are linear under the
lens of lazy evaluation are rejected by Core's current linear type system.

We address this limitation (and its implications on validating and influencing
optimising transformations) by designing a type system which understands
semantic linearity in the presence of laziness and is suitable for the
intermediate language of an optimising compiler.
%
In detail, our contributions are:
%
\begin{itemize}

\item We review background concepts necessary to understand our work, in
Chapter~\ref{sec:background}. Namely, linear type systems and linear types in
Haskell, evaluation strategies, the Core type system ($System~F_C$), and
multiple optimising transformations applied by GHC in its compilation pipeline.

\item We explain and provide insights into \emph{semantic} linearity in
contrast to \emph{syntactic} linearity, in Haskell, by example
($\S$~\ref{sec:linearity-semantically}).

\item We introduce Linear Core, a type system for a linear lazy language with
all key features from Core (except for type equality coercions), which,
crucially, understands semantic linearity in the presence of laziness
($\S$~\ref{sec:main:linear-core}). To the best of our knowledge, this is the
first type system to understand linearity semantically in the context of lazy evaluation.

\item We prove Linear Core to be sound (well-typed Linear Core programs do not
get ``stuck'') \emph{and} prove that multiple optimising transformations (which
currently violate linearity in Core) preserve types and linearity in Linear Core ($\S$~\ref{sec:main:metatheory}).

\item We implement Linear Core as a GHC plugin which typechecks linearity in
all intermediate Core programs produced during the compilation process, showing
it accepts the intermediate programs resulting from (laziness-abusing)
transformations in linearity-heavy Haskell libraries, such as
\texttt{linear-base} ($\S$~\ref{sec:discuss:implementation}).

\item Finally, we discuss related and future work (highlighting so-called
\emph{multiplicity coercions}) in the remainder of Chapter~\ref{sec:discussion}.

\end{itemize}

% This observation lies at the core of our work

% In fact, we are not aware of any linear type system which
% understands linearity in the presence of laziness.

% \todo[inline]{In reality, the Core optimising transformations only expose a
% more fundamental issue in the existing linear types in Haskell -- its mismatch
% with the evaluation model. In call-by-need languages a mention of a variable
% might not entail using that variable - it depends on it being required or not.
% This is not explored at all and we're the first to do so as far as we know}

% Concluding, by extending Core / System $F_C$ with linearity and multiplicity
% annotations such that we can desugar all of Linear Haskell and validate it
% accross transformations taking into consideration Core's call-by-need
% semantics, we can validate the surface level linear type's implementation, we
% can guarantee optimising transformations do not destroy linearity, and we might
% be able to inform optimising transformations with linearity.

% Consider the following recursive let
% definition, where $x$ is a linear variable that must be used exactly once, would
% not typecheck in a source Haskell program since the typechecker cannot tell that
% $x$ is used linearly, but this program might occur naturally in Core from
% transformations on a program that did succesfully typecheck:
% \begin{code}
% letrec f = \case
%         True -> f False
%         False -> x
% in f True
% \end{code}

% Alternatively, one might imagine Haskell being desugared into an intermediate
% representation to which multiple different optimising transformations are
% applied but on which no integrity checks are done

% Despite \emph{want} a linearly-typed core
% because a linearly-typed Core ensures that desugaring
% Haskell and optimising transformations don't destroy linearity.

% In theory, because the Core language must also know about linearity, we should

% A remedy is to use the multiplicity annotations of λq → as cardinality declarations. Formalising
% and implementing the integration of multiplicities in the cardinality analysis is left as future work.

% In theory, we should typecheck \emph{linearity} in \textbf{Core} just the same
% as the typechecking verification we had with the existing type annotations prior
% to the addition of linear types, that is, our Core program with linearity
% annotations should be typechecked after the optimising transformations...

% \todo[inline]{We should discuss the alternative motivation of figuring out how
% to typecheck linearity in the presence of laziness on its own, why its hard and
% how it allows simpler use of linear types since the compiler doesn't constrain
% the programmer so much}

% \todo[inline]{Rather, the linearity x call-by-need should be the original
% motivation, with linear core as the prime example?}

% \todo[inline]{Explain examples of non-trivial interaction of linearity with
% laziness, with both lets and also with case expressions not evaluating
% expressions in WHNF, and otherwise}

% \todo[inline]{Glimpse at how core optimizations can get us into these situations where we have to see this linearity}

% \todo[inline]{Saying, finally, what we are going to do, and that our system is
% capable of seeing linearity in all of these programs, and more -- it is capable
% of typechecking almost all optimising transformations we studied}

% ROMES:TODO: Does this still make sense? I think we can just not say anything, the introduction is finer now.
% \todo[inline]{Conclude by explaining that the document is structured in such a
% way that the payload starts in chapter 3 after delivering the background
% knowledge necessary to read through it (enumerate), and that we revise the
% introduction there, more in depth, assuming understanding of the background concepts}
% Perhaps now we can have a smaller introduction in chapter 3

% \section*{Goals}

% From a high-level view, our goals for the dissertation include:

% \begin{itemize}
% \item Extending Core's type system and type-checking algorithm with additional
% linearity information in order to successfully type-check linearity in Core
% across transformations; DONE
% \item Validating that our type-system accepts programs before and after each
% transformation is applied; WIP Proofs of optimizations
% \item Arguing the soundness of the resulting system (i.e. no semantically
% non-linear programs are deemed linear); DONE (modulo 1)
% \item Implementing our extensions to Core in GHC, the leading Haskell Compiler. NOPE.
% \end{itemize}


\include{chapters/c2.tex}

%\include{chapters/c3.tex}
%
%\include{chapters/c4.tex}
% 
%\include{chapters/c5.tex}
%
%\include{chapters/c6.tex}
%
\include{chapters/c7.tex}

\include{chapters/c8.tex}

\begin{SingleSpace}
\bibliographystyle{abbrv}
\bibliography{references}
\end{SingleSpace}

\appendix

\chapter{Type Safety Proofs}

\section{Type Preservation}

\input{language-v4/proofs/TypePreservationTheorem}

\section{Progress}

\input{language-v4/proofs/ProgressTheorem}

\section{Irrelevance}

\input{language-v4/proofs/WHNFConvSoundness}

\section{Substitution Lemmas}

\input{language-v4/proofs/LinearSubstitutionLemma}

\input{language-v4/proofs/UnrestrictedSubstitutionLemma}

\input{language-v4/proofs/DeltaSubstitutionLemma}

\section{Assumptions}

\input{language-v4/proofs/DeltaLinearLemma}

% \chapter{Optimisations Preserve Types Proofs}
% Should we keep this?
% % 
% \section{Inlining}
% % 
% % \input{language-v4/proofs/optimizations/Inlining}
% % 
% \section{\texorpdfstring{$\beta$}{Beta}-reduction}
% % 
% % \input{language-v4/proofs/optimizations/BetaReduction}
% % 
% \section{Case of known constructor}
% % 
% % \input{language-v4/proofs/optimizations/CaseOfKnownConstructor}
% % 
% \section{Binder-swap}
% % 
% % \input{language-v4/proofs/optimizations/BinderSwap}
% % 
% \section{Let floating}
% % 
% % \input{language-v4/proofs/optimizations/LetFloating}
% % 
% \section{Case of Case}
% % 
% % \input{language-v4/proofs/optimizations/CaseOfCase}

\end{document}

% TODO: - In the letrec case: congratulations on finding an inference algorithm
% (though I will want to see the proof some day, I don't see why it works yet).
% You should clarify that, during linting, you will have a usage environment
% annotation and won't need to run the inference algorithm. This algorithm is
% only needed when you first create a letrec.

