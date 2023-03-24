\documentclass{lwnovathesis}
\usepackage{boldline}
\usepackage{xargs}
\usepackage{todonotes}
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

\newtheorem{theorem}{Theorem}
\newtheorem{lemma}[theorem]{Lemma}

% Glossary
\usepackage[toc]{glossaries}

%%%%%%%%%%%%%%  Color-related things   %%%%%%%%%%%%%%

%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"

\newcommand{\myFor}[2]{\For{$#1$}{$#2$}}
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
\newcommand{\lletrec}[2]{\mathsf{letrec}~#1~\mathsf{in}~#2}
\newcommand{\ccase}[2]{\mathsf{case}~#1~\mathsf{of}~#2}

\title{Type-checking Linearity in Core/System FC}
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
that originate from Core-to-Core optimizing transformations. As such, linearity
typing is effectively disabled, for otherwise disabling optimizations would be
far more devastating.
%
% This dissertation presents an extension to Core's type system that accepts a
The goal of our proposed dissertation is to develop an extension to Core's type
system that accepts a larger amount of programs and verifies that optimizing
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
to, for example, statically guarantee that file handles, socket descriptors,
and allocated memory is freed exactly once (leaks and double-frees become type
errors), and channel-based communication protocols are
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
In Section~\ref{sec:linear-types} we give a formal account of linear types and
provide additional examples.

Despite their promise and their extensive presence in research
literature~\cite{Wadler1990LinearTC,CERVESATO2000133,10.1093/logcom/2.3.297},
the effective design of the combination of linear and non-linear typing is both
challenging and necessary to bring the advantages of linear typing to
mainstream languages.
%
Consequently, few general purpose programming languages have linear
type systems. Among them are Idris 2~\cite{brady:LIPIcs.ECOOP.2021.9},
a linearly and dependently typed language based on Quantitative Type
Theory, Rust~\cite{10.1145/2692956.2663188}, a language whose
ownership types build on linear types to guarantee memory safety
without garbage collection or reference counting, and, more recently,
Haskell~\cite{cite:linearhaskell}, a \emph{purely functional} and
\emph{lazy} language.
% TODO: Extend above: it's the language of our focus

% TODO: Better sentence here, why do we also want linearity in Haskell?
% linear types
Linearity in Haskell stands out from linearity in Rust and Idris 2
due to the following reasons:

\begin{itemize}
    \item Linear types were only added to the language roughly \emph{31 years
        after} Haskell's inception, unlike Rust and Idris 2 which were
        designed with linearity from the start. It is an especially difficult
        endeavour to add linear types to a well-established language with a
        large library ecosystem and many active users, rather than to develop
        the language from the ground up with linear types in mind, and the
        successful approach as implemented in GHC 9.0, the leading Haskell
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
        basis, System~$F_C$~\cite{cite:systemfc}) in Section~\ref{sec:core}.
        % TODO: \item values in rust are linear by default while non-linear is
        % the haskell default?
\end{itemize}
%

% Linear core good
Aligned with the philosophy of having a \emph{typed} intermediate language, the
integration of linearity in Haskell required extending \textbf{Core} with
linear types. Just as a \emph{typed} Core ensures that the translation from
Haskell (dubbed \emph{desugaring}) and the subsequent optimizing
transformations are correctly implemented, a \emph{linearly typed} Core
guarantees that linear resource usage in the source language is not violated by
the translation process and the compiler optimization passes.
%
It is crucial that the program behaviour enforced by linear types is \emph{not}
changed by the compiler in the desugaring or optimization stages (optimizations
should not destroy linearity!) and a linearity aware Core typechecker is key in
providing such guarantees.
%TODO: linearidade pode informar otimizacoes
%
Additionally, a linear Core can inform Core-to-Core optimizing
transformations~\cite{cite:let-floating,peytonjones1997a,cite:linearhaskell} in order to produce
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
The desugaring process from surface level Haskell to Core, and the subsequent
Core-to-Core optimizing transformations, eliminate and rearrange most of the
syntactic constructs through which linearity checking is performed -- often
resulting in programs completely different from the original.

However, these transformed programs that no longer type-check because of
linearity are \emph{semantically linear}, that is, linear resources are still
used exactly once, despite the type-system no longer accepting those programs.
In order to maintain Core linearly-typed accross transformations, Core must be
extended with additional linearity information to allow type-checking linearity
in Core where we currently do not.

% TODO:
% Consider the minimal example of a function that let binds... this is all quite
% hard: the simple let example wouldn't type check in Haskell, so making it
% typecheck in Core would perhaps entail explaining that we also desire to
% typecheck more linearity in Core than in Haskell.
% \begin{code}
% f x = let y = x in y
% \end{code}
% Moreover, I'm re-thinking our definitions for usage and using usage
% environments to type let bindings. $\llet{y = x+1}{y + y}$ might either
% evaluate $x+1$ only once if $y$ is compiled to a heap allocation or twice if
% $y$ is inlined, and twice if it's inlined just once? If we're conservative we
% always assume it could be consumed the maximum amount of times, and our typing
% rule using usage environments would be correct. This simple example raises many
% questions.

% \begin{itemize}
% \item Exemplo de um programa que fica borked pelas otimizacoes
% \item Explicar que moralmente a linearidade nao foi borked, e so a
%   ``sintaxe'' que e insuficiente.
% \item Mencionar (muito brevemente) que com algumas extensoes a
%   informacao disponivel, era possivel validar coisas, que e
%   ultimamente o objectivo deste trabalho.
% \end{itemize}

% \begin{itemize}
% \item é necessário uma extensao ao Core que enriquece a informação de linearidade
% \item para poder ter mais context no qual analisar os programas
% \item mencionar multiplicity annotaitons só depois, e forward reference
% \end{itemize}

Concluding, by extending Core / System $F_C$ with linearity and multiplicity
annotations such that we can desugar all of Linear Haskell and validate it
accross transformations taking into consideration Core's call-by-need
semantics, we can validate the surface level linear type's implementation, we
can guarantee optimizing transformations do not destroy linearity, and we might
be able to inform optimizing transformations with linearity.

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

From a high-level view, our goals for the dissertation include:

% Copiar do outro lado. qual é o objetivo. extender coisas de type syhstem e type checking
% Ser um bocadinho mais concreto sobre a implementação no Core.

\begin{itemize}
\item Extending Core's type system and type-checking algorithm with additional
linearity information in order to successfully type-check linearity in Core
across transformations;
\item Validating that our type-system accepts programs before and after each
transformation is applied;
\item Arguing the soundness of the resulting system (i.e. no semantically
non-linear programs are deemed linear);
\item Implementing our extensions to Core in GHC, the leading Haskell Compiler.
\end{itemize}


\include{chapters/c2.tex}

\include{chapters/c3.tex}

\include{chapters/c4.tex}


\begin{SingleSpace}
\bibliographystyle{abbrv}
\bibliography{references}
\end{SingleSpace}

\end{document}

% TODO: - In the letrec case: congratulations on finding an inference algorithm
% (though I will want to see the proof some day, I don't see why it works yet).
% You should clarify that, during linting, you will have a usage environment
% annotation and won't need to run the inference algorithm. This algorithm is
% only needed when you first create a letrec.

