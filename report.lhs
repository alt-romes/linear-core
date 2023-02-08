\documentclass{lwnovathesis}
 
\usepackage{todonotes}
\usepackage{cmll}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{mathpartir}
\usepackage[ruled,vlined]{algorithm2e}
\usepackage{fancyvrb}
\usepackage{cleveref}
\usepackage{tikz}
\usepackage{tikz-qtree}
\usetikzlibrary{trees}	% this is to allow the fork right path

% Glossary
\usepackage[toc]{glossaries}


%%%%%%%%%%%%%%  Color-related things   %%%%%%%%%%%%%%

%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"

\newcommand{\id}[1]{\textsf{\textsl{#1}}}

\renewcommand{\Varid}[1]{\textcolor{Sepia}{\id{#1}}}
\renewcommand{\Conid}[1]{\textcolor{OliveGreen}{\id{#1}}}

%%%%%%%%%%%%  End of Color-related things   %%%%%%%%%%%%

% It might make sence to add pretty formating of individual things
% like "forall", cf.
% https://github.com/goldfirere/thesis/blob/master/tex/rae.fmt



\DefineVerbatimEnvironment{code}{Verbatim}{fontsize=\small}
\DefineVerbatimEnvironment{example}{Verbatim}{fontsize=\small}

\newcommand{\parawith}[1]{\paragraph{\emph{#1}}}
\newcommand{\lolli}{\multimap}
\newcommand{\tensor}{\otimes}
\newcommand{\one}{\mathbf{1}}
\newcommand{\bang}{{!}}

\newcommand{\llet}[2]{\mathsf{let}~#1~\mathsf{in}~#2}
\newcommand{\ccase}[2]{\mathsf{case}~#1~\mathsf{of}~#2}

\title{Linting Linearity in Core/System FC}
\author{Rodrigo Mesquita}

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

\frontmatter

\maketitle

\xtableofcontents
\xlistoffigures
\xlistoftables
\printglossaries

\mainmatter

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
the motto ``well-typed programs do not go wrong''~\cite{}.


Linear type systems~\cite{cite:linear-logic,cite:barberdill} add expressiveness to existing type systems by
enforcing that certain \emph{resources} (e.g.~a file handle) must be
used \emph{exactly once}.
In
programming 
languages with a linear type system, not using certain resources or using them
twice are flagged as type errors. Linear types can thus be used to,
for example, statically guarantee
that file handles, socket descriptors, and allocated memory is freed exactly
once (leaks and double-frees become type errors)~\cite{},
and channel-based communication protocols are deadlock-free~\cite{},
% implement safe
% high-performance language interoperability~\cite{}, 
%guarantee that quantum entangled states are not duplicated~\cite{}
among other high-level correctness properties.
% handle mutable state safely~\cite{}

% TODO: Chegar mais rápido ao que vou fazer? Aqui?

As an example, consider the following C-like program in which allocated memory
is freed twice. We know this to be the dreaded double-free error which will
crash the program at runtime. Regardless, a C-like type system will accept this
program without any issue.
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
In Section~\ref{linear-types} we give a formal account of linear types and provide additional examples.

Despite their promise and their extensive presence in research
literature~\cite{}, the effective design of the combination of linear and
non-linear typing is both challenging and necessary to bring the advantages of
linear typing to mainstream languages.
%
Consequently, few general purpose programming languages have linear
type systems. Among them are Idris 2~\cite{brady:LIPIcs.ECOOP.2021.9},
a linearly and dependently typed language based on Quantitative Type
Theory, Rust~\cite{10.1145/2692956.2663188}, a language whose
ownership types build on linear types to guarantee memory safety
without garbage collection or reference counting, and, more recently,
Haskell~\cite{cite:linearhaskell}, a \emph{purely functional} and
\emph{lazy} language.

Linearity in Haskell stands out from linearity in Rust and Idris 2
due to the following reasons:

\begin{itemize}
    \item Linear types were only added to the language roughly \emph{31 years
        after} Haskell's inception, unlike Rust and Idris 2 which were
        designed with linearity from the start. It is an especially difficult
        endeavour to add linear types to a well-established language with a
        large library ecosystem and many active users, rather than to develop
        the language from the ground up with linear types in mind, and the
        successful approach as implemented in \Gls{GHC} 9.0, the leading Haskell
        compiler, was based on Linear Haskell~\cite{cite:linearhaskell}, where a
        linear type system designed with retaining backwards-compatibility and
        allowing code reuse across linear and non-linear users of the same
        libraries in mind was described. We describe Linear Haskell in detail in
        Section~\ref{sec:linear-haskell}.

    \item Linear types permeate Haskell down to (its) \textbf{Core}, the
        intermediate language into which Haskell is
        translated. \textbf{Core} is a minimal, explicitly typed,
        functional language, on which multiple
        Core-to-Core optimizing transformations are
        defined. Due to Core's minimal design, typechecking 
        Core programs is very efficient and doing so serves as a sanity check to the
        correction of the source transformations. If the resulting optimized
        Core program fails to typecheck, the optimizing
        transformations (are very likely to) have introduced an error
        in the resulting program. We present Core (and its formal
        basis, System~$F_C$) in Section~\ref{sec:core}.
        % TODO: \item values in rust are linear by default while non-linear is
        % the haskell default?
\end{itemize}
%

% Linear core good
Aligned with the philosophy of having a \emph{typed} intermediate language, the
integration of linearity in Haskell required extending \textbf{Core} with
linear types. Just as \emph{typed} Core ensures that the translation of Haskell
(dubbed \emph{desugaring}) and the subsequent optimizing transformations are
correctly implemented, \emph{linearly typed} Core guarantees that linear
resource usage in the source language is not violated by the translation
process and the compiler optimization passes.
%
It is crucial that the program behaviour enforced by linear types is \emph{not}
changed by the compiler in the desugaring or optimization stages (optimizations
should not destroy linearity!) and a linearity aware Core typechecker is key in
providing such guarantees.
%TODO: linearidade pode informar otimizacoes
%
Additionally, a linear Core can inform Core-to-core optimizing
transformations~\cite{cite:let-floating,peytonjones1997a} in order to produce
more performant programs.


% Linear core actually not so good
% Additionally, while not yet a reality, linearity in Core could be used to inform
% certain program optimizations, i.e. having linear types in Core could be used to
% further optimize certain programs and, therefore, benefit the runtime
% performance characteristics of our programs. For example, Linear Haskell\cite{}
% describes as future work an improvement to the inlining optimization: Inlining
% is a centerpiece program optimization primarily because of the subsequent
% optimizing opportunities unlocked by inlining. However, it relies on a heuristic
% process known as \emph{cardinality analysis} to discover safe inlining
% opportunities. Unfortunately, heuristics can be volatile and fail in identifying
% crucial inlining opportunities resulting in programs that fall short of their
% performance potential. On the contrary, the linearity information could be
% integrated in the analysis and used as a (non-heuristic) cardinality
% \emph{declaration}.

While the current version of Core is linearity-aware (i.e.,~Core has so-called
multiplicity annotations in variable binders), its type system does not (fully)
validate the linearity constraints in the desugared program and essentially
fails to type-check programs resulting from several optimizing transformations
that are necessary to produce efficient object code. The reason for this latter
point is not evidently clear:
%
if we can typecheck linearity in the surface level Haskell why do we fail to do
so in Core?
%
The desugaring process from surface level Haskell to Core and the subsequent
Core-to-Core optimizing transformations eliminate and rearrange most of the
syntactic constructs through which linearity checking is performed.

\begin{itemize}
\item Exemplo de um programa que fica borked pelas otimizacoes
\item Explicar que moralmente a linearidade nao foi borked, e so a
  ``sintaxe'' que e insuficiente.
\item Mencionar (muito brevemente) que com algumas extensoes a
  informacao disponivel, era possivel validar coisas, que e
  ultimamente o objectivo deste trabalho.
 \end{itemize}

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

% Is this program really still linear? Yes, but ...

% If one looks at it 

% Alternatively, one might imagine Haskell being desugared into an intermediate
% representation to which multiple different optimizing transformations are
% applied but on which no integrity checks are done

% Despite \emph{want} a linearly-typed core
% because a linearly-typed Core ensures that desugaring
% Haskell and optimizing transformations don't destroy linearity.

% In theory, because the Core language must also know about linearity, we should

% A remedy is to use the multiplicity annotations of λq → as cardinality declarations. Formalising
% and implementing the integration of multiplicities in the cardinality analysis is left as future work.

% In theory, we should typecheck \emph{linearity} in \textbf{Core} just the same
% as the typechecking verification we had with the existing type annotations prior
% to the addition of linear types, that is, our Core program with linearity
% annotations should be typechecked after the optimizing transformations...

% Even though Linear Haskell was successful in integrating linear types in an
% existing language 
% In spite of the smooth integration of linear types in an existing language
% with regard to backwards compatibility and (re)usability, 

% The advent of linear types in Haskell bring forth

% Besides Haskell's supporting linear
% types according to the said paper, Idris 2\cite{} supports linear types in a
% dependently typed setting, Clean\cite{} has uniqueness types which are closely
% related to linear types, and Rust\cite{} has ownership types which build from
% linear types. 
% released in the Glasgow Haskell Compiler (GHC) version 9.0.
% , and, e.g., avoid the required boilerplate threading of linear resources that
% we will get to know ahead.

% Linear types were introduced in GHC 9.0


% In an attempt to bridge the gap between the theory and practicality of linear
% types, Linear Haskell\cite{} describes , the 9.0 version series of Haskell's
% \emph{de facto} compiler, GHC, supports linear types. However, retrofitting
% linear types to a purely-functional lazy language 

% The main contributions of this thesis are:
% \begin{itemize}
%     \item Core Type system which accepts optimized linear programs
% \end{itemize}

% stores a value to the allocated memory, reads from it and finally frees 

% about the usage of resources in a
% programming language.

\section*{Goals}


\begin{itemize}
\item bla bla and bla
  
\end{itemize}

\chapter{Background and Related Work}

In this section we review the concepts required to understand our work. In
short, we discuss linear types, the Haskell programming language, linear types
as they exist in Haskell (dubbed Linear Haskell), Haskell's main intermediate
language (Core) and its formal foundation (System $F_C$) and, finally, an
overview of GHC's pipeline with explanations of some Core-to-Core optimizing
transformations.

\section{Linear Types\label{sec:linear-types}}

Much the same way type systems can statically eliminate various kinds of
programs that would fail at runtime, such as a program that derreferences an
integer value rather than a pointer, linear type systems can guarantee that
certain errors (regarding resource usage) are forbidden.

In linear type systems~\cite{cite:linear-logic,cite:barberdill}, so called
linear resources must be used \emph{exactly once}. Not using a linear resource
at all or using said resource multiple times will result in a type error. We can
model many real-world resources such as file handles, socket descriptors, and
allocated memory, as linear resources. This way, because a file handle must be
used exactly once, forgetting to close the file handle is a type error, and
closing the handle twice is also a type error.  With linear types, avoiding
leaks and double frees is no longer a programmer's worry because the compiler
can guarantee the resource is used exactly once, or \emph{linearly}.

To understand how linear types are defined and used in practice, we present two
examples of anonymous functions that receive a handle to work with (that must be
closed before returning), we explore how the examples could be disregarded as
incorrect, and work our way up to linear types from them. The first function
ignores the received file handle and returns $\star$ (read unit), which is
equivalent to C's \texttt{void}.
%
\begin{mathpar}
    \lambda h.~\mathsf{return}~\star;
    \and
    \lambda h.~\mathsf{close}~h;~\mathsf{close}~h;
\end{mathpar}

Ignoring the file handle which should have been closed by the function makes the
first function incorrect. Similarly, the second function receives the file
handle and closes it twice, which is incorrect not because it falls short of the
specification, but rather because the program will crash while executing it.
%
Additionally, both functions share the same type, $\texttt{Handle} \to \star$,
i.e.  a function that takes a \texttt{Handle} and returns $\star$. The second
function also shares this type because \texttt{close} has type $\texttt{Handle}
\to \star$.
%
Under a simple type system such as C's, both functions are type correct (the
compiler will happily succeed), but both have erroneous behaviours. The first
forgets to close the handle and the second closes it twice. Our goal is to reach
a type system that rejects these two programs.

The key observation to invalidating these programs is to focus on the function
type going between \texttt{Handle} and $\star$ and augment it to indicate that
\emph{the argument must be used exactly once}, or, in other words, that the
argument of the function must be linear. We take the function type $A \to B$
and replace the function arrow ($\to$) with the linear function arrow ($\lolli$)
%
\footnote{Since linear types are born from a correspondence with linear
logic\cite{cite:linear-logic} (the Curry-Howard isomorphism\cite{curry:34,howard:80}), we
borrow the $\lolli$ symbol and other linear logic connectives to describe linear
types.}
%
operator to denote a function that uses its argument exactly once: $A \lolli B$.
%
Providing the more restrictive linear function signature $\texttt{Handle} \lolli
\star$ to the example programs would make both of them fail to typecheck because
they do not satisfy the linearity specification that the function argument
should only be used exactly once.

% Linear types are a powerful idea because they allow us to statically reason
% about resources in our program. A so called linear resource ?

In order to further give well defined semantics to a linear type system, we
present a linearly typed lambda
calculus~\cite{cite:linear-logic,cite:barberdill}, a very simple language with
linear types, by defining what are syntatically valid programs through the
grammar in Fig.~\ref{fig:llcgrammar} and what programs are well typed through
the typing rules in Fig.~\ref{fig:llcrules}. The language features functions
and function application ($\lolli$), two flavours of pairs, additive ($\with$)
and multiplicative ($\tensor$), a disjunction operator ($\oplus$) to construct
sum types, and the $\bang$ modality operator which constructs an unrestricted
type from a linear one, allowing values inhabiting $\bang A$ to be consumed
unrestrictedly. A typing judgement for the linearly typed lambda calculus has
the form
%
\[ \Gamma; \Delta \vdash M : A \]
%
where $\Gamma$ is the context of resources that may be used unrestrictedly,
that is, any number of times, $\Delta$ is the context of resources that must be
used linearly (\emph{exactly once}), $M$ is the program to type and $A$ is its
type.  When resources from the linear context are used, they are removed from
the context and no longer available, and all resources in the linear context
must be used exactly once.

\begin{figure}[h]
\[
\begin{array}{c}
  \begin{array}{lcl}
    A,B & ::= & \star\\
        & \mid & A \lolli B\\
        & \mid & A \oplus B\\
        & \mid & A \tensor B\\
        & \mid & A \with B\\
        & \mid & \bang A\\
   \end{array}
\qquad
  \begin{array}{lcl}
      M,N & ::= & \star \mid \llet{\star = M}{N} \\
        & \mid & u \\
        & \mid & \lambda u. M \mid M~N\\
        & \mid & \textrm{inl}~M \mid \textrm{inr}~M \mid
        \ccase{M}{\textrm{inl}~u_1 \to N_1;\textrm{inr}~u_2 \to N_2}\\
        & \mid & M \tensor N \mid \llet{u_1 \tensor u_2 = M}{N}\\
        & \mid & M \with N \mid \textrm{fst}~M \mid \textrm{snd}~M \\
        & \mid & \bang M \mid \llet{!u = M}{N} \\
   \end{array}
\end{array}
\]
\caption{Grammar for a linearly-typed lambda calculus}
\label{fig:llcgrammar}
\end{figure}

The function abstraction is typed according to the linear function introduction
rule ($\lolli I$). The rule states that a a function abstraction, written
$\lambda u. M$, is a linear function (i.e. has type $A \lolli B$) given the
unrestricted context $\Gamma$ and the linear context $\Delta$, if the program $M$
has type $B$ given the same unrestricted context $\Gamma$ and the linear context
$\Delta,u{:}A$. That is, if $M$ has type $B$ using $u$ of type $A$ exactly once
besides the other resources in $\Delta$, then the lambda abstraction has the
linear function type.
%
\[
    \infer*[right=($\lolli I$)]
    {\Gamma ; \Delta , u{:}A \vdash M : B}
    {\Gamma ; \Delta \vdash \lambda u. M : A \lolli B}
\qquad
    \infer*[right=($\lolli E$)]
    {\Gamma ; \Delta \vdash M : A \lolli B \and \Gamma ; \Delta' \vdash N : A}
    {\Gamma ; \Delta, \Delta' \vdash M~N : B}
\]
%
Function application is typed according to the elimination
rule for the same type ($\lolli E$). To type an application $M~N$ as $B$, $M$
must have type $A \lolli B$ and $N$ must have type $A$. To account for the
linear resources that might be used while proving both that $M{:}A \lolli B$ and
$N{:}A$, the linear context must be split in two such that both typing judgments
succeed using exactly once every resource in their linear context (while the
resources in $\Gamma$ might be used unrestrictedly), hence the separation of the
linear context in $\Delta$ and $\Delta'$.

The multiplicative pair ($M \tensor N$) is constructed from two linearly typed expressions that
can each be typed with a division of the given linear context, as we see in its
introduction rule ($\tensor I$). Upon deconstruction, the multiplicative pair
elimination rule ($\tensor E$) requires that both of the pair constituents be
consumed exactly once.
%
\[
    \infer*[right=($\tensor I$)]
    {\Gamma ; \Delta \vdash M : A \and \Gamma ; \Delta' \vdash N : B}
    {\Gamma ; \Delta , \Delta' \vdash (M \tensor N) : A \tensor B}
\qquad
    \infer*[right=($\tensor E$)]
    {\Gamma ; \Delta \vdash M : A \tensor B \and \Gamma ; \Delta', u{:}A, v{:}B \vdash N : C}
    {\Gamma ; \Delta , \Delta' \vdash \llet{u \tensor v}{N} : C}
\]
%
On the other hand, the additive pair requires that both elements of the pair can
be proved with the same linear context, and upon deconstruction only one of the
pair elements might be used, rather than both simultaneously.

Finally, the "of-course" operator ($\bang$) can be used to construct a resource that can be
used unrestrictedly ($\bang M$). Its introduction rule ($\bang I$) states that
to construct this resource means to add a resource to the unrestricted context,
which can then be used freely. To construct an unrestricted value, however, the
linear context \emph{must be empty} -- an unrestricted value can only be constructed if
it does not depend on any linear resource.
%
\[
    \infer*[right=($\bang I$)]
    {\Gamma ; \cdot \vdash M : A}
    {\Gamma ; \cdot \vdash !M : !A}
\qquad    \infer*[right=($\bang E$)]
    {\Gamma ; \Delta \vdash M : \bang A \and \Gamma, u{:}A ; \Delta' \vdash N : C}
    {\Gamma ; \Delta, \Delta' \vdash \llet{!u = M}{N} : C}
\]
%
To utilize an unrestricted value $M$, we must bind it to $u$ with $\llet{\bang u
= M}{N}$ which can then be used in $N$ unrestrictedly, because $u$ extends the
unrestricted context rather than the linear context as we have seen thus far.

In section~\ref{sec:linear-haskell} we describe how linear types are defined in
Haskell, a programming language more featureful than the linearly typed lambda
calculus. We will see that the theoretical principles underlying the linear
lambda calculus and linear Haskell are the same, and by studying them in this
minimal setting we can understand them at large.

\begin{figure}[h]
\[
  \begin{array}{c}
    \infer*[right=($u$)]
    { }
    {\Gamma ; u{:}A \vdash u : A}
\qquad
    \infer*[right=($u$)]
    { }
    {\Gamma , u{:}A ; \cdot \vdash u : A}
\\[1em]
    \infer*[right=($\tensor I$)]
    {\Gamma ; \Delta \vdash M : A \and \Gamma ; \Delta' \vdash N : B}
    {\Gamma ; \Delta , \Delta' \vdash (M \tensor N) : A \tensor B}
\quad
    \infer*[right=($\tensor E$)]
    {\Gamma ; \Delta \vdash M : A \tensor B \and \Gamma ; \Delta', u{:}A, v{:}B \vdash N : C}
    {\Gamma ; \Delta , \Delta' \vdash \llet{u \tensor v}{N} : C}
\\[1em]
    \infer*[right=($\lolli I$)]
    {\Gamma ; \Delta , u{:}A \vdash M : B}
    {\Gamma ; \Delta \vdash \lambda u. M : A \lolli B}
\qquad
    \infer*[right=($\lolli E$)]
    {\Gamma ; \Delta \vdash M : A \lolli B \and \Gamma ; \Delta' \vdash N : A}
    {\Gamma ; \Delta, \Delta' \vdash M~N : B}
\\[1em]
    \infer*[right=($\with I$)]
    {\Gamma ; \Delta \vdash M : A \and \Gamma ; \Delta \vdash N : B}
    {\Gamma ; \Delta \vdash M \with N : A \with B}
\quad
    \infer*[right=($\with E_L$)]
    {\Gamma ; \Delta \vdash M : A \with B}
    {\Gamma ; \Delta \vdash \textrm{fst}~M : A}
\quad
    \infer*[right=($\with E_R$)]
    {\Gamma ; \Delta \vdash M : A \with B}
    {\Gamma ; \Delta \vdash \textrm{snd}~M : B}
\\[1em]
    \infer*[right=($\oplus I_L$)]
    {\Gamma ; \Delta \vdash M : A}
    {\Gamma ; \Delta \vdash \textrm{inl}~M : A \oplus B}
\qquad
    \infer*[right=($\oplus I_R$)]
    {\Gamma ; \Delta \vdash M : B}
    {\Gamma ; \Delta \vdash \textrm{inr}~M : A \oplus B}
\\[1em]
    \infer*[right=($\oplus E$)]
    {\Gamma ; \Delta \vdash M : A \oplus B \and \Gamma ; \Delta', w_1{:}A \vdash N_1 : C \and
    \Gamma ; \Delta', w_2{:}B \vdash N_2 : C}
    {\Gamma ; \Delta, \Delta' \vdash \ccase{M}{\textrm{inl}~w_1 \to N_1 \mid \textrm{inr}~w_2 \to N_2} : C}
\\[1em]
    \infer*[right=($\star I$)]
    { }
    {\Gamma ; \cdot \vdash \star : \star}
\quad    \infer*[right=($\star E$)]
    {\Gamma ; \Delta \vdash M : \star \and \Gamma ; \Delta' \vdash N : B}
    {\Gamma ; \Delta, \Delta' \vdash \llet{\star = M}{N} : B}
\\[1em]
    \infer*[right=($\bang I$)]
    {\Gamma ; \cdot \vdash M : A}
    {\Gamma ; \cdot \vdash !M : !A}
\qquad    \infer*[right=($\bang E$)]
    {\Gamma ; \Delta \vdash M : \bang A \and \Gamma, u{:}A ; \Delta' \vdash N : C}
    {\Gamma ; \Delta, \Delta' \vdash \llet{!u = M}{N} : C}
  \end{array}
\]
\caption{Typing rules for a linearly-typed lambda calculus}
\label{fig:llcrules}
\end{figure}

% % \begin{code}
% % let p = malloc(5)
% %     p' = store(p, "x")
% %     (p'', v) = load(p)
% %     free p''
% % \end{code}

% % We'd like to hide the boilerplate involved \cite{Linear constraints}

\section{Haskell}

Haskell is a functional programming language defined by the Haskell
Report~\cite{jones1999haskell,marlow2010haskell} and whose \emph{de-facto}
implementation is GHC, the Glasgow Haskell Compiler~\cite{marlow2012the}. Haskell is a
\emph{lazy}, \emph{purely functional} language, i.e., functions cannot
have side effects or mutate data, and, contrary to many programming languages,
arguments are \emph{not} evaluated when passed to functions, but rather are only
evaluated when its value is needed. The combination of purity and laziness is
unique to Haskell among mainstream programming languages.

Haskell is a large feature-rich language but its relatively small core is based
on a typed lambda calculus. As such, there exist no statements and computation
is done simply through the evaluation of functions. Besides functions, one can
define types and their constructors and pattern match on said constructors.
Function application is denoted by the juxtaposition of the function expression
and its arguments, which often means empty space between terms (\texttt{f~a}
means \texttt{f} applied to \texttt{a}). Pattern matching is done with the
\texttt{case} keyword followed by the enumerated alternatives. All variable
names start with lower case and types start with upper case (excluding type
variables). To make explicit the type of an expression, the \texttt{::} operator
is used (e.g.  $\texttt{f~::~Int}\to \texttt{Bool}$ is read \texttt{f} \emph{has
type} function from \texttt{Int} to \texttt{Bool}).

Because Haskell is a pure programming language, input/ouptut side-effects are
modelled at the type-level through the non-nullary
%
\footnote{\texttt{IO} has kind $\texttt{Type}\to\texttt{Type}$, that is, it is
only a type after another type is passed as a parameter (e.g.  \texttt{IO~Int},
\texttt{IO~Bool}); \texttt{IO} by itself is a \emph{type constructor}}
%
type constructor \texttt{IO}. A value of type \texttt{IO~a} represents a
\emph{computation} that when executed will perform side-effects and produce a
value of type \texttt{a}. Computations that do I/O can be composed into larger
computations using so-called monadic operators, which are like any other
operators but grouped under the same abstraction.
%
Some of the example programs will look though as if they had statements, but,
in reality, the sequential appearence is just syntatic sugar to an expression
using monadic operators. The main take away is that computations that do I/O
may be sequenced together with other operations that do I/O while retaining the
lack of statements and the language purity guarantees.

% TODO: Perhaps elaborate a bit more on the constructors and pattern matching?

As an example, consider these functions that do I/O and their types. The first
opens a file by path and returns its handle, the second gets the size of a file
from its handle, and the third closes the handle. It is important that the
handle be closed exactly once, but currently nothing enforces that usage policy.

\begin{code}
openFile :: FilePath -> IOMode -> IO Handle
hFileSize :: Handle -> IO Integer
hClose   :: Handle -> IO ()
\end{code}

The following function makes use of the above definitions to return the size of
a file given its path. Note that the function silently leaks the handle to the
file, despite compiling successfully.

\begin{code}
countWords :: FilePath -> IO Integer
countWords path = do
    handle <- openFile path ReadMode
    size   <- hFileSize handle
    return size
\end{code}
% hClose handle

Another defining feature of Haskell is its powerful type system. In contrast to
most mainstream programming languages, such as OCaml and Java, Haskell supports a myriad of
advanced type level features, such as:
\begin{itemize}

    \item Multiple forms of advanced polymorphism: where languages with whole
        program type inference usually stick to Damas–Hindley–Milner type
        inference~\cite{DBLP:conf/popl/DamasM82}, Haskell goes much further with, e.g.,
        arbitrary-rank types~\cite{10.1017/S0956796806006034}, type-class
        polymorphism~\cite{10.1145/227699.227700}, levity polymorphism~\cite{10.1145/3062341.3062357},
        multiplicity polymorphism~\cite{cite:linearhaskell}, and, more recently, impredicative
        polymorphism~\cite{10.1145/3408971}.

    \item Type level computation by means of type classes and Haskell's type
        families~\cite{,,}, which permit a direct encoding of type-level
        functions resembling rewrite rules.

    \item Local equality constraints and existential types by using GADTs, which
        we explain ahead in more detail. A design for first class existential
        types with bi-directional type inference in Haskell has been published
        in~\cite{10.1145/3473569}, despite not being yet implemented in GHC.

\end{itemize}
% Haskell's type families, supports abstraction through type classes, and GADTs
% which we explain in more detail ahead.  as type classes, arbitrary-rank types,
% functional dependencies, GADTs, type families and (more recently) even
% impredicative polymorphism\cite{}
These advanced features have become commonplace in Haskell code, enforcing
application level invariants and program correctness through the types. As an
example to work through this section while we introduce compile-time invariants
with \gls{GADT}s, consider the definition of \texttt{head} in the standard library, a
function which takes the first element of a list by pattern matching on the list
constructors.

\begin{code}
    head :: [a] -> a
    head [] = error "List is empty!"
    head (x:xs) = x
\end{code}

When applied to the empty list, \texttt{head} terminates the program with an
error. This function is unsafe -- our program might crash if we use it on an
invalid input.
%
Leveraging Haskell's more advanced features, we can use more expressive types to
assert properties about the values and get rid of the invalid cases (e.g. we
could define a \texttt{NonEmpty} type to model a list that can not be empty).
%
A well liked motto is "make invalid states unrepresentable". In this light, we
introduce Generalized Algebraic Data Types (GADTs) and create a list type
indexed by size for which we can write a completely safe \texttt{head} function
by expressing that the size of the list must be at least one, at the type level.

\subsection{Generalized Algebraic Data Types}

\textbf{GADTs}~\cite{10.1145/1159803.1159811,,,} are an advanced Haskell feature
that allows users to define data types as they would common algebraic data
types, with the added abilitiy to give explicit type signatures for the data
constructors where the result type may differ in the type parameters (e.g., we
might have two constructors of the same data type \texttt{T~a} return values of
type \texttt{T~Bool} and \texttt{T~Int}).
%
This allows for additional type invariants to be represented with GADTs through
their type parameters, which restricts the use of specific constructors and
their subsequent deconstruction through pattern matching.
%
% TODO: Rewrite this bit below
Pattern matching against GADTs can introduce local type refinements, that is,
pattern matching against certain data constructors will refine the type
information used for typechecking individual case alternatives. We develop the
length-indexed lists example without discussing the type system and type
inference details of GADTs which we later explore in~\ref{related-work-gadts}.

% First, we define the natural numbers inductively: a natural number is either
% zero (\texttt{Z}) or a successor (\texttt{S}) of another natural number (e.g.
% the successor of the successor of zero is a natural number). The following
% definition creates the \texttt{Nat} type, the \texttt{Z} and \texttt{S} data
% constructors which construct values, \emph{and} the \texttt{Z} and \texttt{S}
% \emph{type} constructors which construct types.
% %
% % The latter two exist because of the \emph{DataKinds} language feature which
% % promotes term-level constructors to type-level constructors.
% 
% \begin{code}
%     data Nat = Z | S Nat
%   \end{code}

We define the data type in GADT syntax for length-index lists which
takes two type parameters. The first type parameter is the length of the list
and the type of the type parameter (i.e. the kind of the first type parameter)
is \texttt{Nat}. To construct a type of kind \texttt{Nat} we can only use the
type constructors \texttt{Z} and \texttt{S}. The second type parameter is the
type of the values contained in the list, and any type is valid, hence the
\texttt{Type} kind.

\begin{code}
    data Vec (n :: Nat) (a :: Type) where
        Nil :: Vec Z a
        Cons :: a -> Vec m a -> Vec (S m) a
\end{code}

The length-indexed list is defined inductively as either an empty list \emph{of
size zero}, or the construction of a list by appending a new element to an
existing list \emph{of size $m$} whose final size is $m+1$ (\texttt{S m}). The
list \texttt{Cons~'a'~(Cons~'b'~Nil)} has type \texttt{Vec~(S~(S~Z))~Char}
because \texttt{Nil} has type \texttt{Vec~Z~Char} and \texttt{Cons~'a'~Nil} has
type \texttt{Vec~(S~Z)~Char}.
GADTs make possible different data constructors being parametrized over
different type parameters as we do with \texttt{Vec}'s size parameter being
different depending on the constructor that constructs the list.

To define the safe \texttt{head} function, we must specify the type of the input
list taking into account that the size must not be zero. To that effect, the
function takes as input a \texttt{Vec (S n) a}, that is, a vector with size
(n+1) for all possible n's, making a call to \texttt{head} on a list of type
\texttt{Vec Z a} (an empty list) a compile-time type error.

\begin{code}
    head :: Vec (S n) a -> a
    head (Cons x xs) = x
\end{code}

Pattern matching on the \texttt{Nil} constructor is not needed, despite it
being a constructor of \texttt{Vec}. The argument type doesn't match the type
of the \texttt{Nil} constructor ($\texttt{S~n} \neq \texttt{Z}$), so the
corresponding pattern case alternative is innacessible because the typechecker
does not allow calling \texttt{head} on \texttt{Nil} (once again, its type,
\texttt{Vec~Z~a}, does not match the input type of \texttt{head},
\texttt{Vec~(S~n)~a}).

In practice, the idea of using more expressive types to enforce invariants at
compile time, that is illustrated by this simple example, can be taken much
further, e.g., to implement type-safe artificial neural
networks\cite{https://blog.jle.im/entry/practical-dependent-types-in-haskell-1.html},
enforce size compatibility in operations between matrices and vectors\cite{}, to
implement red-black trees guaranteeing its invariants at compile-time, or to
implement a material system in a game engine\cite{}.
% TODO: cite: https://blog.jle.im/entry/practical-dependent-types-in-haskell-1.html
% TODO: haskell-servant?

Linear types are, similarly, an extension to Haskell's type system that makes it
even more expressive, by providing a finer control over the usage of certain
resources at the type level.

% TODO:
% Is it outside the scope of this report to discuss the merits and disadvantages
% of laziness and purely functional properties?

% \begin{itemize}
    % \item Features fundamentais
    % \item Exemplos, introduzir syntax
    % \item (Ao contrário de OCaml) tem um sistema de tipos muito sofisticado
    % \item Eventualmente explicação de GADTs? c/ exemplo do Vec
    % \item Uma das features mais avaçadas/experimentais é o Linear Haskell
% \end{itemize}

\section{Linear Haskell\label{sec:linear-haskell}}

% Introduction of linear types to Haskell. How do they work, what's the syntax?
% Multiplicities, examples. Monads, multiplicity polymorphism, multiplicity
% polymoprhism applied to monadic bind to define resource-aware sequencing of
% operations. Linear haskell relates systemFC with the linear lambda calculus?

The introduction of linear types to Haskell's type system is originally
described in Linear Haskell~\cite{cite:linearhaskell}. While in
Section~\ref{sec:related-work-linear-haskell} we discuss the reasoning and
design choices behind retrofitting linear types to Haskell, here we focus on
linear types solely as they exist in the language, and re-work the file handle
example seen in the previous section to make sure it doesn't typecheck.

A linear function ($f :: A \lolli B$) guarantees that if ($f~x$) is consumed
exactly once, then the argument $x$ is consumed exactly once. The precise
definition of \emph{consuming a value} depends on the value as follows,
paraphrasing Linear Haskell~\cite{cite:linearhaskell}:

\begin{itemize}
    \item To consume a value of atomic base type (like \texttt{Int} or
        \texttt{Ptr}) exactly once, just evaluate it
    \item To consume a function value exactly once, apply it to one argument,
        and consume its result exactly once.
    \item To consume a value of an algebraic datatype exactly once,
        pattern-match on it, and consume all its linear components exactly once.
        For example, a linear pair (equivalent to $\tensor$) is consumed exactly
        once if pattern-matched on \emph{and} both the first and second element are
        consumed once.
\end{itemize}


In Haskell, linear types are introduced through \emph{linearity on the function
arrow}.
In practice, this means function types are annotated with a linearity that
defines whether a function argument must be consumed \emph{exactly once} or
whether it can be consumed \emph{unrestrictedly} (many times).
%
As an example, consider the function $f$ below, which doesn't typecheck because
it is a linear function (annotated with \texttt{1}) that consumes its argument
more than once, and the function $g$, which is an unrestricted function
(annoted with \texttt{Many}) that typechecks because its type allows the
argument to be consumed unrestrictedly.

\begin{minipage}{0.47\textwidth}
\begin{code}
    f :: a %1 -> (a, a)
    f x = (x, x)
\end{code}
\end{minipage}
\begin{minipage}{0.47\textwidth}
\begin{code}
    g :: a %Many -> (a, a)
    g x = (x, x)
\end{code}
\end{minipage}

The function annotated with the \emph{multiplicity} annotation of \texttt{1} is
equivalent to the linear function type ($\lolli$) seen in the linear lambda
calculus~(\Cref{sec:linear-types}).
%
Additionally, algebraic data type constructors can specify whether their
arguments are linear or unrestricted, requiring that, when pattern matched on,
linear arguments be consumed once while unrestricted arguments need not be
consumed exactly once.
%Similarly, when constructing such a constructor, using a linear value as a
%linear argument of the constructor consumes it once, while using it as an
%unrestricted argument consumes it unrestrictedly.
%
To encode the multiplicative linear pair ($\tensor$) we must create a pair data
type with two linear components. To consume an algebraic data type is to
consume all its linear components once, so, to consume said pair data type, we
need to consume both its linear components -- successfully encoding the
multiplicative pair elimination rule ($\tensor E$). To construct said pair data
type we must provide two linear elements, each consuming some required
resources to be constructed, thus encoding the multiplicative pair introduction
rule ($\tensor I$). As such, we define \texttt{MultPair} as an algebraic data
type whose constructor uses a linear arrow for each of the
arguments\footnote{By default, constructors defined without GADT syntax have
linear arguments. We could have written \texttt{data MultPair a b = MkPair a b}
to the same effect.}.

\begin{code}
data MultPair a b where
    MkPair :: a %1 -> b %1 -> MultPair a b
\end{code}

The linearity annotations~\texttt{1} and \texttt{Many} are just a
specialization of the more general so-called \emph{multiplicity annotations}. A
multiplicity of \texttt{1} entails that the function argument must be consumed
once, and a function annotated with it ($\to_1$) is called a linear function
(often written with $\lolli$). A function with multiplicity of \texttt{Many}
($\to_\omega$) is an unrestricted function, which may consume its argument 0 or more times.
Unrestricted functions are equivalent to the standard function type and, in fact,
the usual function arrow ($\to$) implicitly has multiplicity \texttt{Many}.
Multiplicities naturally allow for \emph{multiplicity polymorphism}, which we
explain below.

Consider the functions $f$ and $g$ which take as an argument a function from
@Bool@ to @Int@. Function $f$ expects a linear function ($Bool~\to_1~Int$),
whereas $g$ expects an unrestricted function ($Bool~\to_\omega~Int$).
Function $h$ is a function from @Bool@ to @Int@ that we want to pass as an argument to both $f$
and $g$.

\begin{minipage}{0.47\textwidth}
\begin{code}
f :: (Bool %1 -> Int) -> Int
f c = c True

g :: (Bool -> Int) -> Int
g c = c False
\end{code}
\end{minipage}
\begin{minipage}{0.47\textwidth}
\begin{code}
h :: Bool %m -> Int
h x = case x of
  False -> 0
  True -> 1
\end{code}
\end{minipage}

For the application of $f$ and $g$ to $h$ to be well typed, the multiplicity of
$h$ ($\to_?$) should match the multiplicity of both $f$ ($\to_1$) and
$g$ ($\to_\omega$).
Multiplicity polymorphism allows us to use \emph{multiplicity variables} when
annotating arrows to indicate that the function can both be typed as linear and
as an unrestricted function, much the same way type variables can be used to
define polymorphic functions. Thus, we define $h$ as a multiplicity
polymorphic function ($\to_m$), making $h$ a well-typed argument to both
$f$ and $g$ ($m$ will unify with $1$ and $\omega$ at the call sites).

% \begin{itemize}
    % \item Linear Haskell definition
    % \item Consuming values precisely
    % \item Multiplicities
    % \item Multiplicity polymorphism
    % \item Files example
    % \item Ok talvez acabar abruptamente
    % \item Talvez na próxima. Que relaciona o systemFC com o calculo lambda linear
% \end{itemize}

\section{Core and System $F_C$\label{sec:core}}

Haskell is a large and expressive language with many syntatic constructs and
features. However, the whole of Haskell can be desugared down to a minimal,
explicitly typed, intermediate language called \textbf{Core}.
%
Desugaring allows the compiler to focus on the small desugared language rather
than on the large surface one, which can greatly simplify the subsequent
compilation passes.
%
Core is a strongly-typed, lazy, purely functional intermediate language akin to
a polymorphic lambda calculus, that GHC uses as its key intermediate
representation.
%
To illustrate the difference in complexity, in GHC's implementation of Haskell,
the abstract syntax tree is defined through dozens of datatypes and hundreds of
constructors, while the GHC's implementation of Core is defined in 3 types
(expressions, types, and coercions) and 15 constructors~\cite{cite:ghc-source-code}.
%
The existence of Core and its use is a major design decision in GHC Haskell
with significant benefits which have decidedly proved themselves over
time~\cite{,}:

\begin{itemize}
\item Core allows us to reason about the entirety of Haskell in a much smaller
functional language. Performing analysis, optimizing transformations, and code
generation is done on Core, not Haskell. The implementation of these compiler passes is
significantly simplified by the minimality of Core.
 
\item Since Core is an (explicitly) typed language
(c.f.~System~F~\cite{Girard1972InterpretationFE,10.1007/3-540-06859-7_148}),
type-checking Core serves as an internal consistency check for the desugaring
and optimization passes.
%
The Core typechecker provides a verification layer for the correctness of
desugaring and optimizing transformations (and their implementations) because
both desugaring and optimizing transformations must produce well-typed Core.
 
\item Finally, Core's expressiveness serves as a sanity-check for
all the extensions to the source language -- if we can desugar a
feature into Core then the feature must be sound by reducibility.
Effectively, any feature added to Haskell is only syntatic sugar if it can be
desugared to Core.
\end{itemize}

The implementation of Core's typechecker differs significantly from the Haskell
typechecker because Core is explicitly typed and its type system is based on
the $System~F_C$~\cite{cite:systemfc} type system (i.e., System F extended with
a notion of type coercion), while Haskell is implicitly typed and its type
system is based on the constraint-based type inference system
$OutsideIn(X)$~\cite{cite:outsideinx}. Therefore, typechecking Core is simple,
fast and requires no type inference, whereas Haskell's typechecker must account
for the entirety of Haskell's syntax and must perform type-inference in the
presence of arbitrary-rank polymorphism, existential types, type-level
functions, and GADTs, which are known to introduce significant challenges for
type inference algorithms~\cite{cite:outsideinx}.
%
Haskell is typechecked in addition to Core to (i) perform type inference and (ii)
provide meaningful type errors. If Haskell wasn't typechecked and instead we
only typechecked Core, everything (e.g.  all binders) would have to be
explicitly typed and error messages would refer to the intermediate language
rather than the written program.

The Core language is based on $System~F_C$, a polymorphic lambda calculus with
explicit type-equality coercions that, like types, are erased at compile time
(i.e. types and coercions alike don't incur any cost at run-time). The
syntax of System
$F_C$~\cite{cite:systemfc} terms is given in Figure~\ref{fig:systemfc-terms}, which
corresponds exactly to the syntax of System $F$~\cite{Girard1972InterpretationFE,10.1007/3-540-06859-7_148} with term and (kind-annotated) type abstraction as
well as term and type application, extended with algebraic data types, let-bound
expressions, pattern matching and coercions or casts.

\begin{figure}[h]
\[
\begin{array}{lcll}
    u               & ::=  & x \mid K                           & \textrm{Variables and data constructors}\\
    e               & ::=  & u                                  & \textrm{Term atoms}\\
                    & \mid & \Lambda a{:}\kappa.~e~\mid~e~\varphi  & \textrm{Type abstraction/application}\\
                    & \mid & \lambda x{:}\sigma.~e~\mid~e_1~e_2 & \textrm{Term abstraction/application}\\
                    & \mid & \llet{x{:}\sigma = e_1}{e_2}       & \\
                    & \mid & \ccase{e_1}{\overline{p\to e_2}}   & \\
                    & \mid & e \blacktriangleright \gamma       & \textrm{Cast} \\
                    &      &                                    & \\
    p               & ::= & K~\overline{b{:}\kappa}~\overline{x{:}\sigma} & \textrm{Pattern}
\end{array}
\]
\caption{System $F_C$'s Terms\label{fig:systemfc-terms}}
\end{figure}

Explicit type-equality coercions (or simply coercions), written
$\sigma_1 \sim \sigma_2$, serve as evidence of
equality between two types $\sigma_1$ and $\sigma_2$. A coercion $\sigma_1\sim\sigma_2$ can be used to safely
\emph{cast} an expression $e$ of type $\sigma_1$ to type $\sigma_2$, where
casting $e$ to $\sigma_2$ using $\sigma_1\sim\sigma_2$ is written
$e\blacktriangleright\sigma_1\sim\sigma_2$. The syntax of \emph{coercions} is
given by Figure~\ref{fig:systemfc-types} and describes how coercions can be
constructed to justify new equalities between types (e.g. using symmetry and
transitivity). For example, given $\tau\sim\sigma$, the coercion
$\textbf{sym}~(\tau\sim\sigma)$ denotes a type-equality coercion from $\sigma$
to $\tau$ using the axiom of symmetry of equality. Through it, the expression
$e{:}\sigma$ can be cast to $e{:}\tau$, i.e.
$(e{:}\sigma\blacktriangleright\textbf{sym}~\tau\sim\sigma){:}\tau$.

\begin{figure}[h]
\[
\begin{array}{lcll}
  \sigma,\tau & ::= & d \mid \tau_1~\tau_2 \mid S_n~\overline{\tau}^n \mid \forall a{:}\kappa. \tau & \textrm{Types} \\
  \gamma,\delta & ::= & g \mid \tau \mid \gamma_1~\gamma_2 \mid S_n~\overline{\gamma}^n \mid \forall a{:}\kappa. \gamma & \textrm{Coercions} \\
                & \mid & \textbf{sym}~\gamma \mid \gamma_1\circ\gamma_2 \mid \gamma @@ \sigma \mid \textbf{left}~\gamma \mid \textbf{right}~\gamma \\
  \varphi & ::= & \tau \mid \gamma & \textrm{Types and Coercions}
\end{array}
\]
\caption{System $F_C$'s Types and Coercions\label{fig:systemfc-types}}
\end{figure}


$System~F_C$'s coercions are key in desugaring  advanced type-level Haskell features such as GADTs, type families and newtypes~\cite{cite:systemfc}. In
short, these three features are desugared as follows:
\begin{itemize}
  \item GADTs local equality constraints are desugared into explicit type-equality
  evidence that are pattern matched on and used to cast the branch alternative's
  type to the return type.

  \item Newtypes such as @newtype BoxI = BoxI Int@ introduce a global
  type-equality $\texttt{BoxI}\sim\texttt{Int}$ and construction and
  deconstruction of said newtype are desugared into casts.

  \item Type family instances such as @type instance F Int = Bool@ introduce a
  global coercion $\texttt{F~Int}\sim\texttt{Bool}$ which can be used to cast
  expressions of type $\texttt{F~Int}$ to $\texttt{Bool}$.
\end{itemize}

Core further extends $System~F_C$ with \emph{jumps} and \emph{join
points}~\cite{maurer2017compiling}, allowing new optimizations to be performed
which ultimately result in efficient code using labels and jumps, and
with a construct used for internal notes such as profiling information.

% $System~F_C$ is expressive enough as a target for Haskell

In the context of Linear Haskell, and recalling that Haskell is fully
desugared into Core / System~$F_C$ as part of its validation and
compilation strategy, we highlight the inherent incompatibility of
linearity with Core / System~$F_C$ as a current flaw in GHC that
invalidates all the benefits of Core wrt linearity.  Thus, we must
extend System $F_C$ (and, therefore, Core) with linearity in order to
adequately validate the desugaring and optimizing transformations as
linearity preserving, ensuring we can reason about Linear Haskell in
its Core representation.

% \begin{itemize}
% \item Referencia figura, as can be seen in bla, is a lambda calculus type system with coercions
% \item Figura com syntax do system FC
% \item Coercions
% \item Coercions são para local equalities, type families, func deps, newtypes e etc, tornam possível fazer o desugar das features mais complicadas
% \item No contexto dos linear types ...  Revisitando a idea de desugar para
%        core... system fc...  Esta linguagem as is não suporta linearidade e não
%        permite seguir esta filosofia de "desugar to core" por que Core não suporta,
%        fundamentalmente incompatível com linearidade, e por isso é preciso integrar
%        linearidade no systemFC (consequently no Core)
%\end{itemize}

% \begin{itemize}
    % \item What is Core (IR) e as particularidades
    % \item Em cima do SystemFC
    % \item Optimizações feitas no Core
    % \item Base SystemFC tem de ser "merged" com o linear lambda calculus
    % \item Ou porque é que é importante o Core ter linearidade também/a que nível foi introduzido
    % \item Falar das coercions em especifico
    % \item E das local equalities que são implicitas no front end
% \end{itemize}

\section{GHC Pipeline}

The GHC compiler processes Haskell source files in a series of phases that feed
each other in a pipeline fashion, each transforming their input before passing
it on to the next stage. This pipeline (Figure~\ref{fig:ghc-pipeline}) is 
crucial in the overall design of GHC. We now give a high-level
overview of the phases.

\subsection{Haskell to Core}

\parawith{Parser.} The Haskell source files are first processed by the lexer
and the parser. The lexer transforms the input file into a sequence of valid
Haskell tokens. The parser processes the tokens to create an abstract syntax
tree representing the original code, as long as the input is a syntactically
valid Haskell program.

\parawith{Renamer.} The renamer's main task is to resolve names to fully
qualified names, taking into consideration both existing identifiers in the
module being compiled and identifiers exported by other modules. Additionally,
name ambiguity, variables out of scope, unused bindings or imports, etc., are
all checked and reported as errors or warnings.

\parawith{Type-checker.} With the abstract syntax tree validated by
the renamer and with the names fully qualified, the Haskell program is
type-checked before being desugared into Core.  Type-checking the Haskell
program guarantees that the program is well-typed. Otherwise, type-checking
fails with an error reporting where in the source typing failed.
%
Furthermore, every identifier in the program is annotated with its type.
Haskell is an implicitly typed language and, as such, type-inference must be
performed to type-check programs. During type inference, every identifier is
typed and we can use its type to decorate said identifier in the abstract
syntax tree produced by the type-checker. First, annotating identifiers is
\emph{required} to desugar Haskell into Core because Core is explicitly typed -- to
construct a Core abstract syntax tree the types are indispensable (i.e.
we cannot construct a Core expression without explicit types). Secondly, names
annotated with their types are useful for tools manipulating Haskell, e.g.
for an IDE to report the type of an identifier.

\parawith{Desugaring.} The type-checked Haskell abstract syntax tree is then
transformed into Core by the desugarer. We've discussed in
Section~\ref{sec:core} the relationship between Haskell and Core in detail, so we
refrain from repeating it here. It suffices to say that the desugarer
transforms the large Haskell language into the small Core language by
simplifying all syntactic constructs to their equivalent Core form (e.g.  @newtype@
constructors are transformed into coercions).

\subsection{Core-To-Core Transformations}

The Core-to-Core transformations are the most important set of
optimizing transformations that GHC performs during compilation. By design, the
frontend of the pipeline (parsing, renaming, typechecking and desugaring) does
not include any optimizations -- all optimizations are done in Core.
The transformational approach focused on Core, known as \emph{compilation by
  transformation}, allows transformations to be both modular and simple.
Each transformation focuses on optimizing a specific (set of)
constructs, where applying a transformation often exposes opportunities for
other transformations to fire. Since transformations are modular, they
can be chained and iterated in order to maximize the optimization potential.



% I know this paragraph is useless :)
However, due to the destructive nature of transformations (i.e. applying a
transformation is not reversible), the order in which transformations
are applied determines how well the resulting program is optimized.
As such, certain orderings of optimizations can hide 
optimization opportunities and block them from firing. This phase-ordering
problem~\cite{} is present in most optimizing compilers.

% Techniques such as
% equality saturation~\cite{} bypass the phase-ordering problem because all
% optimizing transformations are applied non-destructively; however, it's a much
% more expensive technique that has not been .
%
% transformation based approach to optimization allows each producing a Core
% program fed to the next optimizing transformation.

Foreshadowing the fact that Core is the main object of our study, we want to type-check
linearity in Core before \emph{and} after each optimizing transformation is
applied (Section~\ref{sec:core}).
%
In that light, we describe below some of the individual Core-to-Core
transformations, using $\Longrightarrow$ to denote a program transformation. In
the literature, the first set of Core-to-Core optimizations was described
in~\cite{santos1995compilation,peytonjones1997a}. These were subsequently
refined and
expanded~\cite{peytonjones2002secrets,baker-finch2004constructed,maurer2017compiling,Breitner2016_1000054251,sergey_vytiniotis_jones_breitner_2017}.
In Figure~\ref{fig:eg:transformations} we present an example that is optimized
by multiple transformations to highlight how the compilation by transformation
process produces performant programs.

% \begin{figure}[h]
% \begin{tikzpicture}
% %Define the function structure
% \tikzset{
%   grow'=right,level distance=25mm, sibling distance =3.5mm,
%   execute at begin node=\strut,
%   every tree node/.style={
% 			draw,
% 			rounded corners,
% 			anchor = west,
% 			minimum width=20mm,
% 			text width=18mm,
% 			align=center,
% 			font = {\scriptsize}},
%          edge from parent/.style={draw, edge from parent fork right}
% }
% %Draw the function structure (top to bottom)
% %distance from root: width of tree
% \begin{scope}[frontier/.style={distance from root=75mm}]
% \Tree
% [.{Overall-\\ Function}
% 		[.{Main-\\ Function A}
% 			[.{Sub-Function\\ A}
% 			\node(f1){Function A};
% 			\node(f2){Function B};
% 			\node(f3){Function C};
% 			]
% 			\node(f4){Function D};
% 		]
% 		[.{Main-\\ Function B}
% 			[.{Sub-Function\\ B}
% 				\node(f5){Function E};
% 				\node(f6){Function F};
% 				\node(f7){Function G};
% 			]
% 			\node(f8){Function H};
% 		]
% 		\node(f9){Function I};
% ]
% \end{scope}
% %Define the product structure
% \tikzset{grow'=left,
% 		sibling distance =3.85mm,
%        edge from parent/.style={
%          draw, edge from parent fork left}
% }
% %Draw the product structure (bottom up)
% %distance from root: width of tree
% %xshift/yshift: Shiftoption of right tree
% \begin{scope}[
% 	frontier/.style={distance from root=75mm},
% 	xshift=190mm,
% 	yshift=4.9mm]
% \Tree
% [.{Product}
% 		\node(p8){Part H};
% 		[.{Module A}
% 			[.{Component B}
% 				\node(p7){Part G};
% 				\node(p6){Part F};
% 				\node(p5){Part E};
% 			]
% 			\node(p4){{Part D}};
% 		]
% 		[.{Module B}
% 			[.{Component A}
% 				\node(p3){Part C};
% 				\node(p2){Part B};
% 				\node(p1){Part A};
% 			]
% 		]
% ]
% \end{scope}
% %Draw the lines between function and product side
%   \draw [thick, >=stealth, dashed]
%         (f1.east)--(p1.west)
%         (f2.east)--(p2.west)
%         (f3.east)--(p3.west)
%         (f3.east)--(p1.west)
%         (f4.east)--(p4.west)
%         (f5.east)--(p5.west)
%         (f6.east)--(p6.west)
%         (f7.east)--(p7.west)
%         (f7.east)--(p6.west)
%         (f8.east)--(p4.west)
%         (f8.east)--(p5.west)
%         (f8.east)--(p8.west)
%         (f9.east)--(p7.west);
% %Draw the headlines
% \begin{scope}[every node/.style = {rounded corners, font = {\normalsize\bfseries}}]
% \node at (5,5) [] {function structure};
% \node at (16,5) [rounded corners] {product structure};
% \end{scope}
% \end{tikzpicture}
% \end{figure}

% Ideia de que há uma transformação .... pipeline... e depois há muitas
% transformações feitas internamente dentro do Core,STG,Cmm,LLVM e que o meu foco
% fundamental é as trasnformações CoreToCore
% 
% Typechecekr sobre o Haskell, é produzido Core com termos anotados
% explicitamente que saem do typechecker do Haskell e depois gera-se código que
% primeiro é preciso optimizar core...
% 
% The architecture of GHC
% Both typecheckers, the backends Core is transformed into, and \textbf{\emph{all
% core transformations}}.

%\begin{itemize}
    % \item Parser to Rename to Typechecker to Desugar
    % \item Core2Core transformations
    % \item GHC unique em haver tantas transformações sempre sobre a mesma intermediate
    %    representation como input e output
%\end{itemize}

% Previous itemize. Talvez ainda tenha de ter secções sobre os últimos dois
% pontos
% \begin{itemize}
%     \item Linear types
%     \item Linear Haskell
%     \item Core
%     \item Sistemas de inferência
%     \item GADTs e Coercions
% \end{itemize}

% like inlining, its inverse (CSE), beta-reduction, lambda-lifting,
% eta-reduction/eta-expansion, binder-swap, case-of-case,
% case-of-know-constructor, float-out, float-in, worker/wrapper split (this one
% is big, in comparison), etc…

\parawith{Inlining.} Inlining is an optimization common to all compilers, but
especially important in functional languages~\cite{peytonjones1997a}. Given
Haskell's pure and lazy semantics, inlining can be employed in Haskell to a much
larger extent because we needn't worry about evaluation order or side effects,
contrary to most imperative and strict languages. \emph{Inlining} consists of
replacing an occurrence of a let-bound variable by its right-hand side:
\[
\llet{x = e}{\dots x \dots}~\Longrightarrow~\llet{x = e}{\dots e \dots}
\]
Effective inlining is crucial to optimization because, by bringing the
definition of a variable to the context in which it is used, many other local
optimizations are unlocked. The work~\cite{peytonjones2002secrets} further
discusses the intricacies of inlining and provides algorithms used for inlining
in GHC.

\parawith{$\beta$-reduction.} $\beta$-reduction is an optimization that
consists of reducing an application of a term $\lambda$-abstraction or
type-level $\Lambda$-abstraction (Figure~\ref{fig:systemfc-terms}) by replacing
the $\lambda$-bound variable with the argument the function is applied to:
\[
(\lambda x{:}\tau.~e)~y~\Longrightarrow~e[y/x]
\qquad
(\Lambda a{:}\kappa.~e)~\varphi~\Longrightarrow~e[\varphi/a]
\]
If the $\lambda$-bound variable is used more than once in the body of the
$\lambda$-abstraction we must be careful not to duplicate work, and we can
let-bound the argument, while still removing the $\lambda$-abstraction, to avoid
doing so:
\[
(\lambda x{:}\tau.~e)~y~\Longrightarrow~\llet{x = y}{e}
\]
$\beta$-reduction is always a good optimization because it effectively evaluates
the application at compile-time (reducing heap allocations and execution time)
and unlocks other transformations.

\parawith{Case-of-known-constructor.} If a \texttt{case} expression is
scrutinizing a known constructor $K~\overline{x{:}\sigma}$, we can simplify the
case expression to the branch it would enter, substituting the pattern-bound
variables by the known constructor arguments ($\overline{x{:}\sigma}$):
\[
\begin{array}{lcl}
\textbf{case}~K~v_1~\dots~v_n~\textbf{of}\\
~~K~x_1~\dots~x_n \to e \\
~~\dots
\end{array}
\Longrightarrow
e[v_i/x_i]_{i=1}^n
\]
Case-of-known-constructor is an optimization mostly unlocked by other
optimizations such as inlining and $\beta$-reduction, more so than by code
written as-is by the programmer. As $\beta$-reduction, this optimization is also
always good -- it eliminates evaluations whose result is known at compile time
and further unblocks for other transformations.


% não gosto da frase abaixo
\parawith{Let-floating.} A let-binding in Core entails performing
\emph{heap-allocation}, therefore, let-related transformations directly impact
the performance of Haskell programs. In particular, let-floating
transformations are concerned with best the position of let-bindings in a
program in order to improve efficiency. Let-floating is an important group of
transformations for non-strict (lazy) languages described in detail
by~\cite{cite:let-floating}. We distinguish three let-floating transformations:
\begin{itemize}
  \item \emph{Float-in} consists of moving a let-binding as far \emph{inwards}
  as possible. For example, it could be moving a let-binding outside of a case
  expression into the branch alternative that uses the let-bound variable:
  \[
  \begin{array}{l}
    \llet{x = y+1\\}{\ccase{z}{\\\ ~[] \to x*x \\~~(p:ps) \to 1}}
  \end{array}
  \Longrightarrow
  \begin{array}{l}
    \ccase{z}{\\\ [] \to \llet{x = y+1}{x*x} \\~(p:ps) \to 1}
  \end{array}
  \]
  This can improve performance by not performing let-bindings (e.g. if the
  branch the let was moved into is never executed); improving strictness
  analysis; and further unlocking other optimizations such as
  ~\cite{cite:let-floating}. However, care must be taken when floating a
  let-binding inside a $\lambda$-abstraction because every time that
  abstraction is applied the value (or thunk) of the binding will be allocated
  in the heap (we briefly revisit this in Section~\ref{sec:rw:let-floating})

  \item \emph{Full laziness} transformation, also known as \emph{float-out},
  consists of moving let-bindings outside of enclosing $\lambda$-abstractions.
  The warning above regarding $\lambda$-abstractions recomputing the binding
  every time they are applied is valid even if bindings are not purposefully
  pushed inwards. In such a situation, floating the let binding out of the
  enclosing lambda can make it readily available across applications of said
  lambda.

  \item The \emph{local transformations} are the third type of let-floating
  optimizations. In this context, the local transformations are local rewrites
  that improve the placement of bindings. There are three local
  transformations:
  \[
  \begin{array}{llcl}
  1. & (\llet{v = e}{b})~a              & \Longrightarrow & \llet{v = e}{b~a} \\
  2. & \ccase{(\llet{v = e}{b})}{\dots} & \Longrightarrow & \llet{v = e}{\ccase{b}{\dots}}\\
  3. & \llet{x = (\llet{v = e}{b})}{c}  & \Longrightarrow & \llet{v = e}{\llet{x = b}{c}} \\
  \end{array}
  \]
  These transformations do not change the number of allocations but potentially
  create opportunities for other optimizations to fire, such as expose a lambda
  abstraction~\cite{cite:let-floating}.
\end{itemize}

\parawith{$\eta$-expansion and $\eta$-reduction.} $\eta$-expansion is a transformation
that expands a function expression $f$ to $(\lambda x. f~x)$, where $x$ is not
free in $f$. This transformation can improve efficiency because it can fully
apply functions which would previously be partially applied by using the
variable bound to the expanded $\lambda$. A partially applied function is often
more costly than a fully saturated one because it entails a heap allocation for
the function closure, while a fully saturated one equates to a function call.
$\eta$-reduction is the inverse transformation to $\eta$-expansion, i.e., a
$\lambda$-abstraction $(\lambda x.  f~x)$ can be $\eta$-reduced to simply $f$.

\parawith{Case-of-case.} The case-of-case transformation fires when a case
expression is scrutinizing another case expression. In this situation, the
transformation duplicates the outermost case into each of the inner case
branches:
\[
\begin{array}{lcl}
\ccase{\left( \begin{array}{c}\ccase{e_c}{\\~alt_{c_1} \to e_{c_1}
                                          \\~\dots
                                          \\~alt_{c_n} \to e_{c_n}}\end{array} \right)}{\\~alt_1 \to e_1
                                                                                        \\~\dots
                                                                                        \\~alt_n \to e_n}
\end{array}
\Longrightarrow
\begin{array}{lcl}
\ccase{e_c}{\\~alt_{c_1} \to \left( \begin{array}{c}\ccase{e_{c_1}}{\\~alt_1 \to e_1
                                                         \\~\dots
                                                         \\~alt_n \to e_n}\end{array} \right)
            \\~\dots
            \\~alt_{c_n} \to \left( \begin{array}{c}\ccase{e_{c_n}}{\\~alt_1 \to e_1
                                                         \\~\dots
                                                         \\~alt_n \to e_n}\end{array} \right)}
\end{array}
\]
This transformation exposes other optimizations, e.g., if $e_{c_n}$ is a known
constructor we can readily apply the \emph{case-of-known-constructor}
optimization. However,
this transformation also potentially introduces significant code
duplication. To this effect,
we apply a transformation that creates \emph{join points} (i.e.,~shared bindings outside
the case expressions that are used in the branch alternatives) that are
compiled to efficient code using labels and jumps.

\parawith{Common sub-expression elimination.}
%
Common sub-expression elimination (CSE) is a transformation that is
effectively inverse to \emph{inlining}.
This transformation factors out expensive expressions into a
shared binding. In practice, lazy functional languages don't benefit nearly as
much as strict imperative languages from CSE and, thus, it isn't very important
in GHC~\cite{aquilo}.

\parawith{Static argument and lambda lifting.} \emph{Lambda lifting} is a
transformation that abstracts over free variables in functions by making them
$\lambda$-bound
arguments~\cite{10.1007/3-540-15975-4_37,santos1995compilation}. This allows
functions to be ``lifted'' to the top-level of the program (because they no
longer have free variables). Lambda lifting may unlock inlining opportunities
and allocate less function closures, since the definition is then created only
once at the top-level and shared across uses.
%
The \emph{static argument} transformation identifies function arguments which
are \emph{static} across calls, and eliminates said \emph{static argument} to
avoid passing the same fixed value as an argument in every function call, which
is especially significant in recursive functions. To this effect, the
\emph{static argument} is bound outside of the function definition and becomes
a free variable in its body. It can be thought of as the transformation inverse
to \emph{lambda lifting}.

% \parawith{Binder-swap.}

\parawith{Strictness analysis and worker/wrapper split.} The strictness
analysis, in lazy programming languages, identifies functions that always
evaluate their arguments, i.e.  functions with (morally) \emph{strict
arguments}. Arguments passed to functions that necessarily evaluate them can be
evaluated before the call and therefore avoid some heap allocations. The
strictness analysis may be used to apply the worker/wrapper split
transformation~\cite{peytonjones1993measuring}. This transformation creates two
functions from an original one: a worker and a wrapper. The worker receives
unboxed values~\cite{10.1007/3540543961_30} as arguments, while the wrapper
receives boxed values, unwraps them, and simply calls the worker function
(hence the wrapper being named as such). This allows the worker to be called in
expressions other than the wrapper, saving allocations and being possibly much
faster, especially if the worker recursively ends up calling itself rather than
the wrapper.

\begin{figure}[t]

\[
\begin{array}{lc}
\begin{array}{l}\textrm{if}~(not~x)~\textrm{then}~e_1~\textrm{else}~e_2\end{array} & \overset{Desugar}{\Longrightarrow}\\
\\
\begin{array}{l}\ccase{not~x}{\\~~\textrm{True}\to e_1\\~~\textrm{False}\to e_2}\end{array} & \overset{Inline~not}{\Longrightarrow} \\
\\
\begin{array}{l}\ccase{\left(\begin{array}{l}\lambda y. \ccase{y}{\\~\textrm{True}\to\textrm{False}\\~\textrm{False}\to\textrm{True}}\end{array}\right)~x}{\\~~\textrm{True}\to e_1\\~~\textrm{False}\to e_2}\end{array} & \overset{\beta-reduction}{\Longrightarrow} \\
\\
\begin{array}{l}\ccase{\left(\begin{array}{l}\ccase{x}{\\~\textrm{True}\to\textrm{False}\\~\textrm{False}\to\textrm{True}}\end{array}\right)}{\\~~\textrm{True}\to e_1\\~~\textrm{False}\to e_2}\end{array} & \overset{Case-of-case}{\Longrightarrow} \\
\\
\begin{array}{l}\ccase{x}{\\~~\textrm{True}\to\left(\begin{array}{l}\ccase{\textrm{False}}{\\~\textrm{True}\to e_1\\~\textrm{False}\to e_2}\end{array}\right)\\~~\textrm{False}\to\left(\begin{array}{l}\ccase{\textrm{True}}{\\~\textrm{True}\to e_1\\~\textrm{False}\to e_2}\end{array}\right)}\end{array} & \overset{Case-of-known-constructor}{\Longrightarrow} \\
\\
\begin{array}{l}\ccase{x}{\\~~\textrm{True}\to e_2\\~~\textrm{False}\to e_1}\end{array} & \square \\
\end{array}
\]

\caption{Example sequence of transformations}
\label{fig:eg:transformations}
\end{figure}

\subsection{Code Generation}

The code generation needn't be changed to account for the work we will do in
the context of this thesis, so we only briefly describe it.

After the core-to-core pipeline is run on the Core program and produces
optimized Core, the program is translated down to the Spineless Tagless
G-Machine (STG) language~\cite{jones_1992}. STG language is a small functional
language that serves as the abstract machine code for the STG abstract machine
that ultimately defines the evaluation model and compilation of Haskell through
operational semantics.

From the abstract state machine, we generate C\texttt{--} (read C minus minus), a C-like language designed
for native code generation, which is finally passed as input to one of the code
generation backends\footnote{GHC is not \emph{yet} runtime retargetable, i.e.
to use a particular native code generation backend the compiler must be built
targetting it.}, such as LLVM, x86 and x64, or (recently) JavaScript and WebAssembly.

\section{Related Work}

% TODO: A brief introduction to the related work section?

\parawith{Formalization of Core}

System $F_C$~\cite{cite:systemfc} (Section~\ref{sec:core}) does not account for
linearity in its formalization, and an extension to System $F_C$ including
linear types has not yet been published. As such, there exists no formal
definition of Core with linearity that accounts for. In this context, we intend to introduce a
linearly typed System $F_C$ with multiplicity annotations and typing rules to
serve as a basis for a linear Core. Critically, this Core linear language must
account for call-by-need evaluation semantics and be valid in light of
Core-to-Core optimizing transformations.

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
of linear types to Haskell comes with added challenges that can not exist in
linearly-typed languages that were designed with linear types from the start:
%
\begin{itemize}
    \item Backwards compatibility. The addition of linear types shouldn't break
        all existing Haskell code.
    \item Code re-usability. The linearly-typed part of Haskell's ecosystem and
        its non-linearly-typed counterpart should fit in together and it must be
        possible to define functions readily usable by both sides
        simultaneously.
    \item Forwards compatibility -- Haskell, despite being an
        industrial-strength language, is also a petri-dish for experimentation
        and innovation in the field of programming languages. Therefore, Linear
        Haskell takes care to accomodate possible future features, in
        particular, its design is forward compatible with affine and dependent
        types.
\end{itemize}
%
Linear Haskell~\cite{cite:linearhaskell} is thus concerned with retrofitting
linear types to Haskell taking into consideration the above design goals, but
not to Haskell's intermediate language which presents its own challenges.

Nonetheless, while the Linear Haskell paper keeps Core unchanged, its
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

Core-to-Core transformations appear in many papers across the research
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

\chapter{Proposed Work}

% \section{Foreword}

% This document is a work in progress proposal that I will deliver (in an extended
% form) at the end of the semester as part of my master thesis preparation. The
% document still needs a proper introduction, lengthy background and related work
% section  such that an outsider might understand what I propose to do. However,
% this initial iteration is instead targeted at those already familiar with the
% problem and serves as a (less bureaucratic) proposal on linting linearity in
% Core and to showcase the preliminary progress I have made so far.


\section{Motivation}

\todo[inline]{ Objectivo desta seccao: contextualizar e descrever o
  problema.
  
Penso que alguma repeticao dos conceitos como a
      definicao textual de linearidade podem cair}


Since the publication of Linear Haskell~\cite{cite:linearhaskell} and its
release in GHC 9.0, Haskell's type system supports linearity annotations in
functions, bringing linear types to a mainstream, pure, and lazy functional
language. Concretely, function types can be annotated with a multiplicity (a
multiplicity of One requires the argument to be consumed exactly once, a
multiplicity of Many allows the argument to be consumed unrestrictedly, i.e.,
zero or more times). A function is linear if it consumes its arguments exactly
once when it itself is consumed exactly once.


\todo[inline]{As mentioned in Section bla, GHC Haskell features two
  typed languages in its pipeline: Haskell and Core. 
  The addition of linear types to GHC Haskell required
  changing the Haskell type system. However ... }

Linearly typed programs are proven/checked to be linear by the type system, so
the addition of linear types evidently required changing the type checker to
support linearity. There exist, however, two distinct type checkers in GHC.
The first is run on the surface language, i.e. the Haskell we write, and is a
complex type checker that now also supports typing linearity. The second is
run on programs written in the intermediate language \emph{Core}, that
are obtained from \emph{desugaring} Haskell.

\todo[inline]{Nao e necessario reexplicar o que e o Core, o que e
  preciso aqui e explicar que o desugaring tem anotacoes de
  linearidade mas que sao ignoradas e explicar porque. Em particular,
  algum do texto que esta mais a frente a dizer as variaveis sao
  anotadas no Core mas que e tudo ignorado deve ficar claro nesta altura}

Core is a much smaller language than the whole of Haskell (even though we
can compile the whole of Haskell to it!) and its type checker is
simple and fast due to Core being explicitly typed. In essence, Core
is close to a higher-order polymorphic lambda calculus. This type
checker (called \emph{Lint}) gives us guarantees of correctness in face of all
the complex transformations a Haskell program undergoes, such as desugaring and
core-to-core optimization passes, because the linter is always run on the resulting code
before ultimately being compiled to (untyped) machine code.

% System FC is the formal system in which the implementation of GHC's intermediate
% representation language \emph{Core} is based on.

We want Core and its type system to give us guarantees about
desugaring and transformations with regard to linearity -- a linearly
typed Core ensures that linearly-typed programs remain correct
(i.e.,~linearity is preserved) after desugaring and all GHC
transformations (i.e.,~optimisations should not destroy linearity).

In this sense, Core is already annotated with linearity, but the \textbf{linter currently
  ignores linearity annotations}.
%
In spite of the strong formal foundations of linear types driving the
implementation, their interaction with the whole of GHC is still far
from trivial. The implemented type system cannot accomodate
several optimising transformations that produce programs that violate
linearity syntactically (i.e.,~multiple occurrences of linear
variables in the program text), but ultimately preserve it in a
semantic sense, where a linear term is still consumed exactly once --
this is compounded by lazy evaluation driving a non-trivial mismatch
between syntactic and semantic linearity.

\todo[inline]{Um exemplo ou dois para ilustrar o problema}

Therefore, linear linting
rejects various valid programs (with regard to linearity) after
desugaring. The current solution to this is to effectively disable the
linear linter, since otherwise disabling optimisations can incur significant
performance costs. However, we believe that GHC's transformations are
correct, and it is the linear linter and its underlying type system
that cannot sufficiently accommodate the
resulting programs.

\section{Goals}

In the upcoming dissertation we will:

\begin{itemize}
\item Propose an extension of Core's type system and type checking algorithm
with additional linearity
information in order to accommodate linear programs in Core that
result from the optimising transformations described in~\autoref{};
\item Argue the soundness of the resulting system (i.e.~no
  semantically non-linear programs are deemed linear);
\item Show how it validates Core-to-Core optimisation
  passes;
\item Implement the extension into GHC's
Core linter.
\end{itemize}


\subsection{Extending Core's type system}

The key design goal of the extension of Core's type system is to
provide enough information so that seemingly syntactically
non-linear but semantically linear programs are equipped with enough
typing information so that they are deemed linearly well-typed, while
ruling out programs that violate linearity from being considered as
linearly typed.
%
To this end, we propose to extend Core's linear type system with
\emph{usage annotations} for let, letrec and case binder bound
variables\todo{dizer pq estes binders especificamente}. Given time, we will also explore a new kind of coercion for
multiplicities to validate programs that combine GADTs with
multiplicities.

\subsubsection{Usage Annotations / Typing Usage Environments}

\todo[inline]{Mover para aqui a parte do que sao as usage annotations
  e como funcionam. Acho que deves apresentar em 2 partes, uma e que
  se tivesses os usage envs bem calculados para tudo, resolvia
  problemas. Outra parte: calcular os usage environments e desafios
  associados. A tua abordagem passa entao por inferir os usage
  environments once and for all quando constrois um letrec, etc, e
  depois usar ``a regra''. Penso que nao precisas de apresentar os
  algoritmos em detalhe. Para apresentares regras, explica bem o que
  elas significam.}


\subsection{Validating the Work}


\todo[inline]{Falar um pouco de como tencionas validar o que
  fazes. Diria que ha a validacao qualitativa obvia -- que
  transformacoes podem agora ser linted ou nao, mas podera ser util
  fazer alguma validacao mais quantitativa e ser util
medir tempos de execucao de coisas (e.g.a construcao dos usage envs)}

\subsection{Tasks and Chronogram}

\todo[inline]{Fazer uma ``expansao'' da lista itemizada que fiz antes mas com mais
detalhe / passos, explicando numa frase ou duas o que cada tarefa e.
Tens uma divisao natural em passos pelos varios binders, alternar com
implementacao no GHC, etc. Nao esquecer de incluir a escrita do
documento final!}



%
The ultimate measure of success is the \verb=-dlinear-core-lint= flag,
which activates the linear linter. In its current implementation,
enabling this flag rejects many linearly valid programs. Ideally, by
the end of our research and implementation, this flag could be enabled by
default and accommodate all existing transformations. Realistically, we want to
accept as many diverse transformations as possible while still preserving
linearity, even if we are unable to account for all of them.

In Section~\ref{typingUsageEnvs} we describe usage environments and how they
solve three distinct problems. In Section~\ref{multiplicityCoercions} we discuss
the beginning of multiplicity coercions. In Section~\ref{examples} we take
programs that are currently rejected and show how the type system with our
extensions can accept them.

% to be able to preserve linearity accross the stages and to enable \emph{Lint} to
% preserve our sanity regarding linearity and eventually inform with linearity new
% transformations.

% A value allocated to be passed to a linear function and then never again used could
% bypass garbage collection.

% Our key innovation is that, by recognising join points as a language construct,
% we both preserve join points through subsequent transformations and exploit them
% to make those transformations more effective. Next, we formalize this ap-
% proach; subsequent sections develop the consequences.

\section{Typing Usage Environments\label{typingUsageEnvs}}

Haskell has call-by-need semantics that entail that an expression is not
evaluated when it is let-bound but rather when the binding variable is used.
This makes it challenging to reason about linearity for let-bound variables. The
following example fails to typecheck in Haskell, but semantically it is indeed
linear due to lazy evaluation:

\begin{code}
f :: a %1 -> a
f x = let y = x in y
\end{code}

Despite not being accepted by the surface-level language, linear programs using
lets occur naturally in Core due to optimising transformations that create let
bindings. In a similar fashion, programs which violate syntatic linearity
for other reasons other than let bindings are produced by Core transformations.

The solution we found to a handful of problems regarding binders is to have a
\emph{usage environment}. A usage environment is a mapping from variables to
multiplicities. The main idea is to annotate those binders with a usage
annotation rather than a multiplicity (in contrast, a lambda-bound variable has
exactly one multiplicity). When we find a bound variable with a usage
environment, we type linearity as if we were using all variables with
corresponding multiplicities from that usage environment.

In the above example, this would amount to annotating $y$ with a usage
environment $x := 1$ (because the expression bound by $y$ uses $x$ one time).
Upon using $y$, we are actually using $x$ one time, and therefore linearity is
preserved.

% The first set of problems appears in the core-to-core optimisation passes. GHC
% applies many optimising transformations to \emph{Core} and we believe those
% transformations preserve linearity. However, Core's linear type system cannot check
% that they indeed preserve linearity.

% The simpler examples come from straightforward and common optimising
% transformations. Then we have recursive let definitions that don't accommodate
% linearity even though it might converge to only use the value once. Finally, we
% have the empty case expression introduced with the \emph{EmptyCase} language
% extension that Core currently can't typecheck either.

% The key idea is to annotate every variable with either its multiplicity, if it's
% lambda bound, or with its usage environment, if it's let bound.

% A usage environment is a mapping from variables to multiplicities.

% When we lint a core expression, we get both its type and its usage environment.
% That means that to lint linearity in an expression, whenever we come across a
% free variable we compute its usage environment and take it into account

% TODO: When we type an expression we get both the type and usage environment

\subsection{Let}

Let bindings in Core are the first family of problems we tackle with usage
environment annotations. Multiple transformations can introduce let-bindings,
such as CSE and join points. By extending the type system to allow let-bindings in Core
we start paving the way to a linear linter.

Currently, every variable in Core is annotated with a multiplicity at its binding
site. The multiplicity for let-bound variables must be ignored throughout the
transformation pipeline or otherwise too many valid programs would be
rejected for violating linearity in its transformed type.

However, programs with let bindings can be correctly typed by associating a
usage environment to the bound variables. Instead of associating a multiplicity
to every binder, we want to associate a multiplicity if the variable is lambda
bound and a usage environment when it is let-bound. We then instantiate the usage
environment solution to lets in particular -- a let bound variable is annotated
with the usage environment computed from the binder expression; in the let body
expression, when we find an occurrence of the let bound variable we emit its
usage environment. The typing rule is the following:

\begin{mathparpagebreakable}
    \infer*[right=(let)]
    {\Gamma \vdash t : A \leadsto \{U\} \\
     \Gamma ; x :_{U} A \vdash u : C \leadsto \{V\}}
    {\Gamma \vdash \text{let } x :_{U} A = t \text{ in } u : C \leadsto \{V\}}
\end{mathparpagebreakable}

Take for example an expression in which $y$ and $z$ are lambda-bound with a
multiplicity of one. In the following code it might not appear as if $y$
and $z$ are both being consumed linearly, but indeed they are since in the first
branch we use $x$ -- which means using $y$ and $z$ linearly -- and we use $y$
and $z$ directly on the second branch. Note again that let binding $x$ doesn't
consume $y$ and $z$ because of lazy evaluation. Only \emph{using} $x$ consumes $y$ and
$z$.

\begin{code}
let x = (y, z) in
case e of
  Pat1 -> … x …
  Pat2 -> … y … z …
\end{code}

If we annotate the $x$ bound by the let with a usage environment $\delta$
mapping all free variables in its binder to a multiplicity ($\delta = [y := 1, z
:= 1]$), we could, upon finding $x$, simply emit that $y$ and $z$ are consumed
once. When typing the second branch we'd also see that $y$ and $z$ are used
exactly once. Because both branches use $y$ and $z$ linearly, the whole case
expression uses $y$ and $z$ linearly.

% Currently, in GHC, we don't annotate let-bound variables with a usage
% environment, but we already calculate a usage environment and use it to check
% some things (which things?)

% \begin{itemize}
%     \item occurrences? store usage environment in Ids (vars)
%     \item Recursive lets (can it be rewritten using fix)
%     \item Empty case expression
% \end{itemize}

% \subsection{Inlining}

% If we annotate the let bound variables with their usage and emit that usage when
% we come across those variables, we can solve the linearity issues with inlining.

\subsection{Recursive Lets}

A recursive let binds a variable to an expression that might use the bound
variable in its body. Certain optimisations can create a recursive let that uses
linearly bound variables in its binder body. We want to treat recursive lets
similarly to lets: attribute to bound variables a usage environment and emit it
when the variable is used.
% TODO: Replace "certain" with concrete examples

The challenging part about determining the usage environment of the variables bound
by a recursive let is knowing what usage to emit inside their own body, when
computing said usage environment. The example below uses $x$ linearly % \ref{example_letrec}
but how can we prove it? If we are able to somehow compute $f$'s usage
environment to $x := 1$, we know $x$ is used once when $f$ is applied to
$\mathit{True}$.

\begin{code}
letrec f = \case
        True -> f False
        False -> x
in f True
\end{code}

The key idea to computing the usage environment of multiple variables that use
themselves in their definition body is to perform the computation in two separate passes. First,
calculate a naive environment by emiting free variables multiplicities as usual
while treating the recursive-let bound variables as free ones. Second, pass the
variables names and their corresponding naive environment as input to
algorithm~\ref{computeRecUsages} to get a final usage environment. Intuitively,
the algorithm, for each recursive binder, iterates over all (initially naive) usage
environments and substitutes the recursive binder by the corresponding usage
environment, scaled up by the amount of times that recursive binder is used in
the environment being updated.

The algorithm for computing the usage environment of a set of
recursive definitions works as follows. An at least informal proof
that the algorithm is correct should eventually follow this.

\begin{itemize}
    \item Given a list of functions and their naive environment computed from
        the body and including the recursive function names ($(f, F), (g, G),
        (h, H)$ in which there might exist multiple occurrences of $f, g, h$ in $F, G, H$
    \item For each bound rec var and its environment, update all bindings and
        their usage as described in the algorithm
    \item After iterating through all bound rec vars, all usage environments
        will be free of recursive bind usages, and hence "final"
\end{itemize}

Note that the difficulty of calculating a usage environment for $n$
recursive-let bound variables increases quadratically, i.e. the algorithm has
$O(n^2)$ complexity, but this is not a problem since it's rare to have more than
a handful of binders in the same recursive let block.

% TODO: I should probably use the re-computed usageEnvs instead of the naiveUsageEnvs.
% I'm pretty sure it might fail in some inputs if I keep using the naiveUsageEnvs.
\begin{algorithm}
$usageEnvs \gets naiveUsageEnvs.map(fst)$\;
\For{$(bind, U) \in naiveUsageEnvs$}{
    \For{$V \in usageEnvs$}{
        $V \gets sup(V[bind]*U\setminus\{bind\}, V\setminus\{bind\})$
    }
}
\caption{computeRecUsages\label{computeRecUsages}}
\end{algorithm}

Putting the usage environment idea together with the algorithm we obtain the following typing rule:

\begin{mathparpagebreakable}
    \infer*[right=(letrec)]
    {\Gamma ; x_1 : A_1 \dots x_n : A_n \vdash t_i : A_i \leadsto \{U_{i_\text{naive}}\} \\
     (U_1 \dots U_n) = \mathit{computeRecUsages}(U_{1_\text{naive}} \dots U_{n_\text{naive}}) \\
     \Gamma ; x_1 :_{U_1} A_1 \dots x_n :_{U_n} A_n \vdash u : C \leadsto \{V\}}
    {\Gamma \vdash \text{let } x_1 :_{U_1} A_1 = t_1 \dots x_n :_{U_n} A_n = t_n \text{ in } u : C \leadsto \{V\}}
\end{mathparpagebreakable}

Instantiating the usage environment solution according to the above description,
here's an informal proof that the previous example is well typed: We %\ref{example_letrec}
compute the naive usage environment of $f$ to be $x := 1, f := 1$. We compute
its actual usage environment by scaling the naive environment of $f$ without $f$
by the amount of times $f$ appears in the naive environment of $f$ ($1*[x :=
1]$) and get $x := 1$. Finally, we emit $x := 1$ from applying $f$ in the let's
body.

% Following the idea of making let-bound variables remember the usage environment
% here's an informal description that that example is well typed. We want to
% anotate the let-bound variable $f$ with a usage environment delta $\delta$, and
% use the binding body to compute it.

% Description of computing usage environment of a case expression:
% https://gitlab.haskell.org/ghc/ghc/-/wikis/uploads/355cd9a03291a852a518b0cb42f960b4/minicore.pdf.

% However, not understanding it, my take would be that we can compute the usage
% environment of every branch of the case expression and make sure that they all
% unify (wrt to submultiplicities). The special case is when the branch happens to
% call $f$ itself while computing the usage environment of $f$. If it were another
% let bound variable we'd add its own usage environment to the one we're
% computing; if it were a lambda bound variable we'd add [itself $:=$ its
% multiplicity].

% My idea is that we can emit a special usage [$rec := p$], which, when unified
% against the other case branches $\delta$ will always succeed with a unification
% mapping from $rec \rightarrow p\delta$ scaled by the multiplicity of $rec$

% So taking the example, to compute the usage environment of $f$, we'd compute for
% the second branch $[x := 1]$ and for the first branch $[rec := 1]$. Then, we'd
% unify them with $rec \rightarrow [x := 1*1]$, and somehow result in $[x := 1]$

The next example is a linearly invalid program because $x$ is a %~\ref{example_letrec_2}
linearly bound variable that is used more than once, and shows how this method
correctly rejects it.

\begin{code}
letrec f = \case
         True -> f False + f False
         False -> x
    in f True
\end{code}

To compute the usage environment of $f$ we take its naive environment to be $x
:= 1, f := 2$. Then, we compute the final environment to be $x := 1$ scaled by
the usage of $f$, $2*[x := 1]$, resulting in $x := 2$. Now, to lint the
linearity of the whole let we must ensure the body of the let uses $x$ linearly.
We emit from the body the usage environment of $f$ ($x := 2$) which uses $x$
more than once, i.e. not linearly.

% To compute the usage environment of $f$ we take the second branch usage
% environment $[x := 1]$ and the first branch usage $[rec := 1+1]$ and unify them,
% somehow resulting in $[x := 2]$. Now, to lint the linearity in the whole let
% expression we must ensure that the body of the let uses $x$ linearly. The body
% is $f True$, which is a let-bound variable (how to distinguish functions that
% must be applied vs variables) so we take its usage environment $[x := 2]$ which
% does not use $x$ linearly and thus breaks linearity.

% \textbf{Re-explained:} to compute the usage environment of the recursive
% let-bound function $f$ when applied, we compute $Z$ such that for all branch
% alternatives $U,V,...$, $U \subset Z$, $V \subset Z$ and so on by tracking the
% multiplicities and usage environments of variables that show up in the body and
% by emitting a special keyword $rec$ everytime we find a saturated call of $f$
% (how to handle unsaturated calls?) (how to have a more general solution that
% doesn't require a keyword, perhaps something to do with fixed points); Then we
% scale $Z \setminus \{(rec,_)\}$ by $Z[rec]$ and get $T$ which is the usage
% environment of $f$ when saturated.

% \textbf{Example 1 revisited:}
% \begin{enumerate}
%     \item Take $U = \{rec := 1\}$
%     \item Take $V = \{x := 1\}$
%     \item Take $Z = \{x := 1, rec := 1\}$
%     \item Take $\pi = Z[rec] = 1$
%     \item Take $W = Z \setminus \{rec\} = \{x := 1\}$
%     \item Take $T = \pi W = \{x := \pi * 1\} = \{x := 1\}$
%     \item Linearity OK
% \end{enumerate}

% \textbf{Example 2 revisited:}
% \begin{enumerate}
%     \item Take $U = \{rec := 2\}$
%     \item Take $V = \{x := 1\}$
%     \item Take $Z = \{x := 1, rec := 1\}$
%     \item Take $\pi = Z[rec] = 2$
%     \item Take $W = Z \setminus \{rec\} = \{x := 1\}$
%     \item Take $T = \pi W = \{x := \pi * 1\} = \{x := 2\}$
%     \item Linearity not OK
% \end{enumerate}


% Draft typing rule:

% In haskell that would look like this;
% \begin{code}
% computeRecUsageEnvs :: [(Var, UsageEnv)] -- Recursive usage environments associated to their recursive call
%                     -> [(Var, UsageEnv)] -- Non-recursive usage environments
% computeRecUsageEnvs l =
%   foldl (flip \\(v,vEnv) -> map \\(n, nEnv) -> (n, ((fromMaybe 0 \$ v `M.lookup` nEnv) `scale` (M.delete v vEnv)) `sup` (M.delete v nEnv))) l l

% sup :: UsageEnv -> UsageEnv -> UsageEnv
% sup = M.merge M.preserveMissing M.preserveMissing (M.zipWithMatched \$ \_ x y -> max x y)

% scale :: Mult -> UsageEnv -> UsageEnv
% scale m = M.map (*m)
% \end{code}

\subsection{Handling the case binder\label{casebinder}}

% (though in the rule seems to only start counting after the second usage which
% would make the rule wrong for a case expression that doesn't use the binder --
% the scrutinee should also be consumed)
The current typing rule for case expressions describes that using the case
binder is as using the case scrutinee multiple times, so we scale the usage of
the case scrutinee by the superior multiplicity of using the case binder across
all branches. However, we hypothetize that this prevents us from typing many
valid programs and ultimately does not correctly capture the usage of a
variable and present a seemingly viable alternative.

Firstly, we recall the definition of \emph{consuming a value} from Linear
Haskell as
\begin{itemize}
    \item Consuming an atomic value is forcing it to Normal Form (NF)
    \item Consuming a value that is constructed with more than 1 argument is
        consuming all of its arguments
\end{itemize}
and further note that when an expression is scrutinized by a case expression it
is evaluated to Weak Head Normal Form (WHNF), which in the case of a nullary data
constructor is equal to NF.

Now, with the following example, my interpretation of the current rule dictates
that the case expression consumes the scrutinee twice because the case binder is
used. However, we know that in the branch where $z$ is used, $z$ is equal to
False, and using False does not violate linearity since we can unrestrictedly
create nullary data constructors. A situation similar to this one below happens
after the CSE transformation.
\begin{code}
    case <complex expression> of z {
        False -> case y of z' { DEFAULT -> z }
        True  -> y
    }
\end{code}
% $\leadsto U$ 

A different example is using the case binder $z$ instead of the arguments we
pattern matched on $x,y$. This currently violates linearity because both $x$ and
$y$ aren't used and because $z$ is used twice. This doesn't typecheck in the
frontend either. However, we know that in this branch, using $z$ is effectively
the same as using $(x,y)$!
\begin{code}
    case <complex expression> of z {
        (x,y) -> z
    }
\end{code}
% $\leadsto U$ 

The good news is that both these programs (and a handful of others listed in
Section~\ref{examples}) are accepted with a new rule we have devised for the
linear linter. We still need to prove we don't accept any invalid programs as
valid.

The key idea of the case-binder-usage solution is \textbf{annotating the case binder
with independent usage environments for each pattern match}. That is, for
each of the possible branches, using the case binder $z$ will equate to
using its usage environment in that branch. That makes it so that using the
case binder instead of a nullary data constructor is the same, using the case
binder instead of reconstructing the value with the bound pattern variables too,
and other situations in which we previously couldn't typecheck linearity are
now accepted.

The typing rule for the case expression using the case binder solution:

\begin{mathparpagebreakable}
    \infer*[right=(case)]
    {\Gamma \vdash t : D_{\pi_1 \dots \pi_n} \leadsto \{U\} \\
     \Gamma ; z :_{U_k} D_{\pi_1 \dots \pi_n} \vdash b_k : C \leadsto \{V_k\}
     \and V_k \leq V}
    {\Gamma \vdash \text{case } t \text{ of } z :_{(U_1\dots U_n)} D_{\pi_1 \dots \pi_n} \{b_k\}_1^m : C \leadsto \{U + V\}}
\end{mathparpagebreakable}

Taking the first example in this section, we annotate both branches (True and
False) with $U_z = \emptyset$ because the pattern match doesn't introduce any
new variables. We consume \emph{complex expression} once and $y$ once, and then use
$z$ once. However, using $z$ once equates to not using anything (semantically
this relates to being able to use False or True unrestrictedly) and therefore
linearity is preserved.

In the second example, we know annotate the only branch with usage environment
$U_z = [x := 1, y := 1]$. Upon the usage of $z$ we emit $x$ and $y$ --
effectively using both -- thus linearity is preserved.

\section{Multiplicity Coercions\label{multiplicityCoercions}}

The second set of problems arises from our inability to coerce a multiplicity
into another (or say that one is submultiple of another?).

% When we pattern match on a GADT we ...

Taking the following example we can see that we don't know how to say
that x is indeed linear in one case and unrestricted in the other, even though
it is according to its type. We'd need some sort of coercion to coerce through
the multiplicity to the new one we uncover when we pattern match on the GADT
evidence (...)

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


% \section{Novel rules}

% \subsection{The usage environment in a Recursive Let}

% \subsection{The usage environment of a Case Binder\label{caseBinderKey}}


% \begin{mathparpagebreakable}
%     \infer*[right=(letrec)]
%     {\Gamma ; \Delta/ \Delta' ; \Omega \vdash M : A \Uparrow \and \Gamma ;
%     \Delta/ \Delta'' ; \Omega \vdash N : B \Uparrow \and \Delta' = \Delta''}
%     {\Gamma ; \Delta/\Delta' ; \Omega \vdash  (M \with N) : A \leadsto U}
% \end{mathparpagebreakable}


\section{Examples\label{examples}}

In this section we present worked examples of programs that currently fail to
compile with \textbf{-dlinear-core-lint} but would succeed according to the
novel typing rules we introduced above. Each example belongs to a subsection
that indicates after which transformation the linting failed.

\subsection{After the desugarer (before optimizations)}

The definition for $\$!$ in \textbf{linear-base}\cite{linearbase} fails to lint after the
desugarer (before any optimisation takes place) with \emph{Linearity failure in
lambda: x 'Many $\not\subseteq$ p}
\begin{code}
($!) :: forall {rep} a (b :: TYPE rep) p q. (a %p -> b) %q -> a %p -> b
($!) f !x = f x
\end{code}

The desugared version of that function follows below. It violates (naive?)
linearity by using $x$ twice, once to force the value and a second time to call
$f$. However, the $x$ passed as an argument is actually the case binder and it
must be handled in its own way. The case binder is the key (as seen
in~\ref{casebinder}) to solving this
and many other examples.
\begin{code}
($!)
  :: forall {rep :: RuntimeRep} a (b :: TYPE rep) (p :: Multiplicity)
            (q :: Multiplicity).
     (a %p -> b) %q -> a %p -> b
($!)
  = \ (@(rep :: RuntimeRep))
      (@a)
      (@(b :: TYPE rep))
      (@(p :: Multiplicity))
      (@(q :: Multiplicity))
      (f :: a %p -> b)
      (x :: a) ->
      case x of x { __DEFAULT -> f x }
\end{code}

% Intuitively, this program is linear because forcing the polymorphic value to
% WHNF ...? Need better semantics of consuming
%
The case binder usage rule typechecks this program because $x$ is consumed once,
the usage environment of the case binder is empty ($x :_\emptyset a$) and,
therefore, when $x$ is used in $f(x)$, we use its usage environment which is
empty, so we don't use anything new.

\emph{How are strictness annotations typed in the frontend? The issue is this program
consumes to value once to force it, and then again to determine the return
value.}

% Work better the meaning of consumption (does it mean for a value to be reduced
% to WHNF?). Is consuming = forcing? Why is the above program linear?

As a finishing note on this example, we show the resulting program from
\textbf{-ddump-simpl} that simply uses a different name for the case binder.
\begin{code}
($!)
  :: forall {rep :: RuntimeRep} a (b :: TYPE rep)
            (p :: Multiplicity) (q :: Multiplicity).
     (a %p -> b) %q -> a %p -> b
($!)
  = \ (@(rep :: RuntimeRep))
      (@a)
      (@(b :: TYPE rep_aSJ))
      (@(p :: Multiplicity))
      (@(q :: Multiplicity))
      (f :: a %p -> b)
      (x :: a) ->
      case x of y { __DEFAULT -> f_aDV y }
\end{code}
% So in this program we use another name for the case binder, but it still stands
% for the resulting of evaluating to WHNF; how is it technically different?

\subsection{Common Sub-expression Elimination}

Currently, the CSE seems to transform a linear program that pattern matches on
constant and returns the same constant into a program that breaks linearity that
pattern matches on the argument and returns the argument (where in the frontend
a constant equal to the argument would be returned)

The definition for $\&\&$ in \textbf{linear-base} fails to lint after the common
sub-expression elimination (CSE) pass transforms the program.
\begin{code}
(&&) :: Bool %1 -> Bool %1 -> Bool
False && False = False
False && True = False
True && x = x
\end{code}
The issue with the program resulting from the transformation is $x$ being used
twice in the first branch of the first case expression. We pattern match on y to
force it (since it's a type without constructor arguments, forcing is consuming)
and then return $x$ rather than the constant $False$
\begin{code}
(&&) :: Bool %1 -> Bool %1 -> Bool
(&&) = \ (x :: Bool) (y :: Bool) ->
  case x of w1 {
    False -> case y of w2 { __DEFAULT -> x };
    True -> y
  }
\end{code}
At a first glance, the resulting program is impossible to typecheck linearly.

The key observation is that after $x$ is forced into either $True$ or $False$,
we know $x$ to be a constructor without arguments (which can be created
without restrictions) and know that where we see $x$ we can as well have
$True$ or $False$ depending on the branch. However, using $x$ here is very
unsatisfactory (and linearly unsound?) because $x$ might be an expression, and
we can't really associate $x$ to the value we pattern matched on (be it $True$
or $False$). What we really want to have instead of $x$ is the $w1$ case binder --
it relates directly to the value we pattern matched on, it's a variable rather
than an expression, and, most importantly, our case-binder-usage idea could be
applied here as well

% Idea: if $x$ was anotated with some information regarding the CSE then perhaps
% it could be typechecked (in a system that considered said anotations) -- This is
% too specific and the case binder environment solution is much cleaner. It just
% requires that the example is changed into using the case binder $w1$ rather than
% $x$.

The solution with the unifying case binder usage idea means annotating the case
binder with its usage environment. For $True$ and $False$ (and other data
constructors without arguments) the usage environment is always empty (using
them doesn't entail using any other variable), meaning we can always use the
case binder instead of the actual constant constructor without issues.
%
Concretely, if we had $w1$ instead of the second occurrence of $x$, we'd have
an empty usage environment for $w1$ in the $False$ branch ($w1 :_\emptyset
Bool$) and upon using $w1$ we wouldn't use any extra resources


To make this work, we'd have to look at the current transformations and see
whether it would be possible to ensure that CSEing the case scrutinee would
entail using the case binder instead of the scrutinee. I don't know of a
situation in which we'd really want the scrutinee rather than the case binder,
so I hypothetize the modified transformation would work out in practice and
solve this linearity issue.


% In this exact example, the binder has usage environment empty ($w1 := []$),
% meaning that in the False branch, when we use $x$, if we instead used $w1$ which
% is equivalent and seems more correct (since it doesn't need the case scrutinee
% expression to be a variable), then the usage of $w1$ would imply the usage of
% $[]$ which is nothing and therefore we would preserve linearity

Curiously, the optimised program resulting from running all transformations
actually does what we expected it with regard to using the constant constructors
and preserving linearity. So is the issue from running linear lint after a
particular CSE but it would be fine in the end?
\begin{code}
(&&) :: Bool %1 -> Bool %1 -> Bool
(&&) = \ (x :: Bool) (y :: Bool) ->
  case x of {
    False -> case y of { __DEFAULT -> GHC.Types.False };
    True -> y
  }
\end{code}

\subsection{Compiling ghc with -dlinear-core-lint}

From the definition of $\mathit{groupBy}$ in $\mathit{GHC.Data.List.Infinite}$:

\begin{code}
groupBy :: (a -> a -> Bool) -> Infinite a -> Infinite (NonEmpty a)
groupBy eq = go
  where
    go (Inf a as) = Inf (a:|bs) (go cs)
      where (bs, cs) = span (eq a) as
\end{code}

We get a somewhat large resulting core expression, in the middle of which the
following expression with a linear type -- which currently syntatically violates
linearity.

\begin{code}
jp :: ([a], Infinite a) \%1 -> (# [a], Infinite a #)
jp (wwj :: ([a], Infinite a)) =
    case wwj of wwj {
        DEFAULT -> case wwj of { (wA, wB) -> (# wA, wB #) }
    }
\end{code}

Using the case binder usage solution, the case binder is annotated with a usage
environment for the only branch ($U_wwj = \emptyset$) and using $wwj$ is equal
to using the $\emptyset$. Here it would mean that second \textbf{case of} $wwj$
doesn't actually use any variables and hence the first $wwj$ isn't used twice.


% \begin{code}
% groupBy = \ (@a) (eq :: a -> a -> Bool) (eta :: Infinite a) ->
%   letrec {
%     go :: Infinite a -> Infinite (NonEmpty a)
%     go = \ (inf :: Infinite a) -> case inf of {
%       Inf x xs -> let {
%         ds :: ([a], Infinite a)
%         ds = let {
%             parteq :: a -> Bool
%             parteq = eq x
%         } in
%           letrec {
%             goZ :: Infinite a -> ([a], Infinite a)
%             goZ = \ (inf' :: Infinite a) -> case wgo inf' of { (# wA, wB #) -> (wA, wB) };

%             wgo :: Infinite a -> (# [a], Infinite a #)
%             wgo = \ (inf' :: Infinite a) -> case inf' of wildX2 {
%               Inf y ys ->
%                 join {
%                     jp :: ([a], Infinite a) \%1 -> (# [a], Infinite a #)
%                     jp (wwj :: ([a], Infinite a)) =
%                         case wwj of wwj {
%                             DEFAULT -> case wwj of { (wA, wB) -> (# wA, wB #) } }
%                     } in
%                       case parteq y of {
%                         False ->
%                             let {
%                                 ww :: ([a], Infinite a)
%                                 ww = ([] @a, wildX2)
%                             } in jump jp ww;
%                         True ->
%                             let {
%                                 dy :: ([a], Infinite a)
%                                 dy = case wgo ys of { (# wA, wB #) -> (wA, wB)
%                                 }
%                             } in
%                                 let {
%                                     wwB :: [a]
%                                     wwB = case dy of { (bs, cs) -> bs }
%                                 } in
%                                     let {
%                                         wwA :: [a]
%                                         wwA = : @a y wwB
%                                     } in let {
%                                         wwC :: Infinite a
%                                         wwC = case dy of { (bs, cs) -> cs }
%                                     } in let {
%                                         ww :: ([a], Infinite a)
%                                         ww = (wwA, wwC)
%                                     } in jump jp ww
%                                 }
%               };
%           } in
%               case wgo xs of { (# wA, wB #) -> (wA, wB) }
%       } in
%           Inf @(NonEmpty a) (:| @a x (case ds of { (bs, cs) -> bs })) (case ds of { (bs, cs) -> go cs })
%     };
%   } in go eta
% \end{code}
% The issue is in the linear function that shows up in the core output (how does
% the linearity end up there?). The wwj variable is used once in the case
% expression, bound as the case binder, and used in the case body once again. Why
% do we do that instead of pattern matching right away? Seems a bit redundant.

% Observation: If the branch is DEFAULT, then the case binder binds the case
% scrutinee which was just forced?, but hasn't been actually consumed, because we
% haven't consumed its components. As long as the same branch doesn't consume the
% pattern matching result and the case binder at the same time it should be fine?

% In this example, we force wwj with the case binder, but we don't really
% consume it (more precise definition of consume...), so we can use the case
% binder meaning we're simply using x for the first time. Needs to be
% formalised....


\subsection{Artificial examples}

Following the difficulties in consuming or not consuming the case binder and its
associated bound variables linearly we constructed some additional examples that
bring out the problem quite clearly.
\begin{code}
case x of w1
    (x1,x2) -> case y:Bool of
                DEFAULT -> (x1,x2)
\end{code}
Is equal to (note that the case binder is being used rather than the $x$ case
scrutinee which could be an arbitrary expression and hence really cannot be
consumed multiple times?)
\begin{code}
case x of w1
    (x1,x2) -> case y:Bool of
                DEFAULT -> w1
\end{code}

We initially wondered whether x was being consumed if the pattern match ignored
some of its variables. We pose that if it does have wildcards then it isn't
consuming x fully
\begin{code}
case x of w1
    (_,x2) -> Is x being consumed? no because not all of its components are
    being consumed?
\end{code}

Can we have a solution that even handles weird cases in which we pattern match
twice on the same expression but only on one constructor argument per time? I
don't think so.
\begin{code}
case exp of w1
    (x1,_) -> case w1 of w2
                (_, x2) -> (x1, x2)
\end{code}

A double let rec in which both use a linear bound variable $y$
\begin{code}
letrec f = \case
        True  -> y
        False -> g True
       g = \case
        True -> f True
        False -> y
    in f False
\end{code}

We have to compute the usage environment of f and g.
For f, we have the first branch with usage environment $y$ and the second with
usage $g$, meaning we have $F = \{g := 1, y := 1\}$
For g, we have $G = \{f := 1, y := 1\}$. To calculate the usage environment of
$f$ to emit upon $f False$, we calculate ...

Refer to the algorithm for computing recursive environment


% \section{Work in progress}

% % \section{Core to Core Validation}
% \subsection{Inlining}

% \subsection{CSE}

% \subsection{Join Points}

% When duplicating a case (in the case-of-case transformation), to avoid code
% explosion, the branches of the case are first made into join points

% \begin{code}
% case e of
%   Pat1 -> u
%   Pat2 -> v
% ~~>
% let j1 = u in
% let j2 = v in
% case e of
%   Pat1 -> j1
%   Pat2 -> j2
% \end{code}

% If there is any linear variable in u and v, then the standard
% let rule above will fail (since j1 occurs only in one branch, and
% so does j2).

% However, if j1 and j2 were annotated with their usage environment,

% \subsection{Empty Case}

% For case expressions, the usage environment is computed by checking all branches
% and taking sup. However, this trick doesn't work when there are no branches.

% \begin{itemize}
% \item https://gitlab.haskell.org/ghc/ghc/-/issues/20058
% \item https://gitlab.haskell.org/ghc/ghc/-/issues/18768

% \item (1) Just like a case expression remembers its type (Note [Why does Case have a
% 'Type' field?] in Core.hs), it should remember its usage environment. This data
% should be verified by Lint.

% \item (2) Once this is done, we can remove the Bottom usage and the second field of
% UsageEnv. In this step, we have to infer the correct usage environment for empty
% case in the typechecker.
% \end{itemize}

% \begin{code}
% {-# LANGUAGE LinearTypes, EmptyCase #-}
% module M where

% {-# NOINLINE f #-}
% f :: a %1-> ()
% f x = case () of {}
% \end{code}

% This example is well typed: a function is linear if it consumes its argument
% exactly once when it's consumed exactly once. It seems like the function isn't
% linear since it won't consume x because of the empty case, however, that also
% means f won't be consumed due to the same empty case, thus linearity is
% preserved.

% \begin{code}
% * In the case of empty types (see Note [Bottoming expressions]), say
%   data T
% we do NOT want to replace
%   case (x::T) of Bool {}   -->   error Bool "Inaccessible case"
% because x might raise an exception, and *that*'s what we want to see!
% (#6067 is an example.) To preserve semantics we'd have to say
%    x `seq` error Bool "Inaccessible case"
% but the 'seq' is just such a case, so we are back to square 1.
% \end{code}

% There are three different problems:

% \begin{itemize}
% \item castBottomExpr converts (case x :: T of {}) :: T to x.
% \item Worker/wrapper moves the empty case to a separate binding
% \item CorePrep eliminates empty case, just like point 1 (See -- Eliminate empty
%     case in GHC.CoreToStg.Prep
% \end{itemize}

% With castBottomExpr, we get the example above to
% \begin{code}
%     f = \ @a (x (%1) :: a) -> ()
% \end{code}
% And if we don't, 
% \begin{code}
%     f = \ @a (x (%1) :: a) -> case () of {}
% \end{code}
% And that supposedly if we had a usage environment in the case expression we
% could avoid the error. How is it typed without the transformation in face
% of the bottom? (Even knowing that theoretically it's because of divergence?)

\bibliographystyle{plain}
\bibliography{references}

\end{document}

% TODO: - In the letrec case: congratulations on finding an inference algorithm
% (though I will want to see the proof some day, I don't see why it works yet).
% You should clarify that, during linting, you will have a usage environment
% annotation and won't need to run the inference algorithm. This algorithm is
% only needed when you first create a letrec.
