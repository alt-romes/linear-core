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
\usepackage{makecell}
\usepackage{thmtools, thm-restate}

% font stack: acmart
% \RequirePackage[T1]{fontenc}
% \RequirePackage[tt=false,type1=true]{libertine}
% \RequirePackage[varqu]{zi4}
% \RequirePackage[libertine]{newtxmath}

\newtheorem{theorem}{Theorem}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{lemma}[theorem]{Lemma}%[theorem]
\newtheorem{sublemma}{Lemma}[lemma]
\newtheorem{assumption}{Assumption}

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
\definecolor{working}{rgb}{0.9,1,0.9}
\newmdenv[hidealllines=true,backgroundcolor=working,innerleftmargin=0pt,innerrightmargin=0pt,innertopmargin=-3pt,innerbottommargin=-3pt,skipabove=3pt,skipbelow=3pt]{working}
\newcommand{\workingcolorname}{light green}

\definecolor{notyet}{rgb}{1,1,0.85}
\newmdenv[hidealllines=true,backgroundcolor=notyet,innerleftmargin=0pt,innerrightmargin=0pt,innertopmargin=-3pt,innerbottommargin=-3pt,skipabove=3pt,skipbelow=3pt]{notyet}
\newcommand{\notyetcolorname}{light yellow}

\definecolor{noway}{rgb}{1,0.9,0.9}
\newmdenv[hidealllines=true,backgroundcolor=noway,innerleftmargin=0pt,innerrightmargin=0pt,innertopmargin=-3pt,innerbottommargin=-3pt,skipabove=3pt,skipbelow=3pt]{noway}
\newcommand{\nowaycolorname}{light red}

\definecolor{limitation}{rgb}{1.0, 0.875, 0.75}
\newmdenv[hidealllines=true,backgroundcolor=limitation,innerleftmargin=0pt,innerrightmargin=0pt,innertopmargin=-3pt,innerbottommargin=-3pt,skipabove=3pt,skipbelow=3pt]{limitation}
\newcommand{\limitationcolorname}{light orange}

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

\title{Type-checking Linearity in Core:\\ Semantic Linearity for a Lazy Optimising Compiler}
\author{Rodrigo Mesquita \\ Advisor: Bernardo Toninho}
\date{ }


\begin{document}

\frontmatter

\maketitle
\cleardoublepage

\chapter*{Acknowledgements}
It would not have been possible to complete this work without the support of
many, to whom I'm deeply thankful.

First and foremost, I'd like to thank my advisor, Bernardo Toninho, for
mentoring and working with me the past two years. Bernardo first introduced me
to programming language theory and Haskell, with a seemingly innocent
undergraduate research project on synthesis from linear types -- catapulting me
into the glorious world and community of PLT, functional programming, and of
the Glasgow Haskell Compiler. Thank you for matching my curiosity by teaching
me so much (in such a short time), for the bright discussions, and great
insights.

Second, I'm thankful to Arnaud Spiwack and Krzysztof Gogolewski for the
invaluable discussions regarding linearity in GHC out of which this work first emerged.
%
I'd also like to thank my GHC colleagues and friends, particularly, Ben Gamari,
Matthew Pickering, Sam Derbyshire, Andreas Klebinger, Sebastian Graf, and John
Ericson, for sharing your expertise, exchanging exciting new ideas, and
teaching me in the ways of the Glorious Glasgow Haskell Compiler.
%
% I'm very thankful to Simon Peyton Jones, for his brilliance as a computer
% scientist, writer, and speaker -- 
%
% From the department, I thank also professor João Leitão for challenging me,
% and professor Mário Pereira, Prof. Mário emprestou-me dois livros do Pierce
% :P Prof Leitão for challenging me ...

I thank my dear friends, and, namely, David Neves, Miguel Costa, Francisco
Pisco, André Costa, Guilherme Gil, Henrique Ferreira, Tomás Santos, and the
Gabinete 248 crew, for great conversations and time well-spent (both working,
and not working) together; and, of course, António Canteiro, whose prolonged
deep friendship is irreplaceable.

I'm deeply grateful for my father Miguel, mother Helena, sister Catarina and
brother Tiago, my grandparents Augusto, Domingos, Eugénia, Conceição,
great-grandparents Gil and Luísa, my aunts, uncles and cousins, and my dearest
beloved Bárbara: for their unwavering support in my every dream or need, and
for their love.

\cleardoublepage

\pdfbookmark{Abstract}{Abstract}
\chapter*{Abstract}
Linear type systems guarantee linear resources are used \emph{exactly once}.
Traditionally, using a resource is synonymous with its \emph{syntactic}
occurrence in the program, however, under the lens of \emph{lazy} evaluation,
linearity can be further understood \emph{semantically}, where a
syntactic occurrence of a resource does not necessarily entail
\emph{using} that resource when the program is evaluated.
%
Semantic linearity is especially necessary in optimising compilers for
languages combining linearity and laziness: optimisations leverage laziness to
heavily rewrite the source program, pushing the interaction of linearity and
laziness to its limit, regardless of the original program typing linearity
conservatively.
%
We present Linear Core, the first type system that understands semantic
linearity in the presence of laziness, suitable for the Core intermediate
language of the Glasgow Haskell Compiler. We prove Linear Core is both type
safe and that multiple optimising transformations preserve linearity in Linear
Core while failing to do so in Core. We have implemented Linear Core as a
compiler plugin to validate the system against linearity-heavy libraries,
including \texttt{linear-base}, in the heart of the compiler.

\cleardoublepage

%%% PREPARATION ABSTRACT %%%
%Linear types were added both to Haskell and to its Core intermediate language,
%which is used as an internal consistency tool to validate the transformations a
%Haskell program undergoes during compilation.
%%
%However, the current Core type-checker rejects many linearly valid programs
%that originate from Core-to-Core optimising transformations. As such, linearity
%typing is effectively disabled, for otherwise disabling optimizations would be
%far more devastating.
%%
%% This dissertation presents an extension to Core's type system that accepts a
%The goal of our proposed dissertation is to develop an extension to Core's type
%system that accepts a larger amount of programs and verifies that optimising
%transformations applied to well-typed linear Core produce well-typed linear
%Core.
%%
%Our extension will be based on attaching variable \emph{usage environments} to
%binders, which augment the type system with more  fine-grained contextual
%linearity information, allowing the system to accept programs which seem to
%syntactically violate linearity but preserve linear resource usage. We will
%also develop a usage environment inference procedure and integrate the
%procedure with the type checker.  We will validate our proposal by showing a
%range of Core-to-Core transformations can be typed by our system.

\pdfbookmark{Resumo}{Resumo}
\chapter*{Resumo}
Num sistema de tipos linear, recursos lineares têm de ser usados
\emph{exatamente uma vez}. Usar um recurso linear costuma ser equivalente a uma
ocorrência \emph{sintática} do mesmo no programa, no entanto, sob a perspectiva
de avaliação \emph{lazy}, a linearidade pode ser também compreendida de forma
\emph{semântica}, observando que uma ocorrência sintática de um recurso não
significa necessariamente que esse recurso seja usado quando o programa é
avaliado.
%
Linearidade semântica é particularmente relevante em compiladores que optimizam
linguagens com linearidade e \emph{laziness}: a \emph{laziness} permite ao
compilador transformar consideravelmente o programa original, de tal forma que
a interacção entre linearidade e \emph{laziness} é levada ao extremo,
independentemente de como a linearidade foi tipificada no programa original.
%
Desenvolvemos o primeiro sistema de tipos (\emph{Linear Core}) que compreende
linearidade semântica na presença de \emph{laziness}, um sistema adequado para
a linguagem intermédia (\emph{Core}) do Glasgow Haskell Compiler. Provamos que
o sistema é \emph{type safe} e que várias optimizações preservam linearidade no
Linear Core, apesar de as mesmas não a preservarem no Core. Implementamos o
Linear Core como um \emph{plugin} para o compilador com o objectivo de validar
o sistema em bibliotecas lineares populares.
\cleardoublepage

%%% PREPARATION ABSTRACT %%%
%Tipos lineares foram integrados ambos no Haskell e na sua linguagem intermédia,
%Core, que serve como uma ferramenta de consistência interna do compilador que
%valida as transformações feitas nos programas ao longo do processo de
%compilação.
%%
%No entanto, o sistema de tipos do Core rejeita programas lineares válidos que
%são produto de optimizações Core-to-Core, de tal forma que a validação da
%linearidade ao nível do sistema de tipos não consegue ser desempenhada com
%sucesso, sendo que a alternativa, não aplicar optimizações, tem resultados
%bastante mais indesejáveis.
%%
%O objetivo da dissertação que nos propomos a fazer é extender ao sistema de
%tipos do Core de forma a aceitar mais programas lineares, e verificar que as
%optimizações usadas não destroem a linearidade dos programas.
%%
%A nossa extensão parte de adicionar \emph{ambientes de uso} às variáveis,
%aumentando o sistema de tipos com informação de linearidade suficiente para
%aceitar programas que aparentemente violam linearidade sintaticamente, mas que
%a preservam a um nível semântico. Para além do sistema de tipos, vamos
%desenvolver um algoritmo de inferência de \emph{ambientes de uso}. Vamos
%validar a nossa proposta através do conjunto de transformações Core-to-Core que
%o nosso sistema consegue tipificar.

\xtableofcontents
\xlistoffigures
% \xlistoftables
% \printglossaries

\begingroup
\pdfbookmark{\listtheoremname}{\listtheoremname}
\listoftheorems
\cleardoublepage
\endgroup  

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

% Statically safe programming languages provide compile time correctness
% guarantees by having the compiler rule out certain classes of errors
% or invalid programs. Moreover, static typing
% allows programmers to state and enforce (compile-time) invariants
% relevant to their problem domain.
% In this sense, type safety entails that all
% possible executions of a type-correct program cannot exhibit behaviors
% deemed ``wrong'' by the type system design. This idea is captured in
% the motto ``well-typed programs do not go wrong''.%~\cite{}.


Linear type systems~\cite{cite:linear-logic,cite:barberdill} add expressiveness
to existing type systems by enforcing that certain \emph{resources} (e.g.~a
file handle) must be used \emph{exactly once}.
%
In programming languages with a linear type system, not using certain resources
or using them twice is flagged as a type error. Linear types can thus be used
to, for instance, statically guarantee that socket descriptors are closed or
heap-allocated memory is freed, exactly once (leaks and double-frees become
type errors), or guarantee channel-based communication protocols are
deadlock-free~\cite{10.1007/978-3-642-15375-4_16},
% implement safe
% high-performance language interoperability~\cite{}, 
%guarantee that quantum entangled states are not duplicated~\cite{}
among other correctness properties~\cite{10.1145/3373718.3394765,10.1145/3527313,cite:linearhaskell}.
% handle mutable state safely~\cite{}

% TODO: Chegar mais rápido ao que vou fazer? Aqui?

Consider the following program in which allocated memory is freed twice.
% We know this to be the dreaded double-free error which will crash the program at runtime.
Regardless of the \emph{double-free} error, a C-like type system will accept this
program without any issue:
% \centering
\begin{code}
let p = malloc(4);
in free(p);
   free(p);
\end{code}
Under the lens of a linear type system, consider the variable $p$ to be a
linear resource created by the call to \texttt{malloc}. Since $p$ is linear, it
must be used \emph{exactly once}.  However, the program above uses $p$ twice,
in the two calls to \texttt{free}. With a linear type system, the
program above does not typecheck! In this sense, linear typing
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
% a linearly and dependently typed language based on Quantitative Type Theory,
Rust~\cite{10.1145/2692956.2663188}, a language whose
ownership types build on linear types to guarantee memory safety
without garbage collection or reference counting, and, more recently,
Haskell~\cite{cite:linearhaskell}, a pure, functional, and
\emph{lazy} general purpose programming language.
%
% Besides Haskell's supporting linear
% types according to the said paper, Idris 2\cite{} supports linear types in a
% dependently typed setting, Clean\cite{} has uniqueness types which are closely
% related to linear types, and Rust\cite{} has ownership types which build from
% linear types. 
%
Linearity in Haskell stands out from linearity in other languages for the
following reasons, essential to our work:

\begin{itemize}
    % \item Linear types were only added to the language roughly \emph{31 years
    %     after} Haskell's inception, unlike Rust and Idris 2 which were designed
    %     with linearity from the start. It is an especially difficult endeavour
    %     to add linear types to a well-established language with a large library
    %     ecosystem and many active users, rather than to develop the language
    %     from the ground up with linear types in mind. The successful
    %     approach as implemented in the Glasgow Haskell Compiler (GHC), the leading
    %     Haskell compiler, is based on Linear Haskell~\cite{cite:linearhaskell}, which describes a linear type system designed
    %     with retaining backwards-compatibility and allowing code reuse across
    %     linear and non-linear users of the same libraries.
    %     We describe Linear Haskell in detail in Section~\ref{sec:linear-haskell}.

    \item Linear types permeate Haskell down to (its) Core, the
        intermediate language into which Haskell is
        translated. Core is a minimal, explicitly typed,
        functional language, to which multiple
        Core-to-Core optimising transformations are
        applied during compilation. Due to Core's minimal design, typechecking
        Core programs is very efficient and doing so serves as a sanity check to the
        correction of the source transformations. If the resulting optimised
        Core program fails to typecheck, the optimising
        transformations are very likely to have introduced an error
        in the resulting program. We present Core and its formal
        basis, System~$F_C$~\cite{cite:systemfc}, in Section~\ref{sec:core}.
        % TODO: \item values in rust are linear by default while non-linear is
        % the haskell default?

    \item Both Haskell and its intermediate language Core are \emph{lazily}
        evaluated, i.e., expressions in Haskell are only evaluated when needed,
        unlike C or Rust, which are \emph{eagerly} evaluated.
        %
        Laziness allows an optimising compiler to aggressively transform the source
        program without changing its semantics and, indeed, the Glasgow Haskell
        Compiler (GHC) heavily transforms Core by leveraging its laziness.
        %
        However, lazy evaluation interacts non-trivially with linearity.
        Intuitively, since expressions are not necessarily evaluated, an
        occurrence of a linear resource in an expression does not necessarily
        entail consuming that resource (i.e., if the expression is not evaluated,
        the resource is not used).

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
process and the compiler optimisation passes.
%
It is crucial that a program's behaviour enforced by linear types is \emph{not}
changed by the compiler in the desugaring or optimisation stages (optimisations
should not destroy linearity!) and a linearity aware Core type-checker is key in
providing such guarantees -- it would be disastrous if the compiler, e.g.,
duplicated a pointer to heap-allocated memory that was previously just used
once and then freed in the original program.
%TODO: linearidade pode informar otimizacoes
%
Even more, linearity in Core can inform Core-to-Core optimising
transformations~\cite{cite:let-floating,peytonjones1997a,cite:linearhaskell},
including inlining and $\beta$-reduction, to produce more performant programs.

% Linear core actually not so good
% Additionally, while not yet a reality, linearity in Core could be used to inform
% certain program optimisations, i.e. having linear types in Core could be used to
% further optimise certain programs and, therefore, benefit the runtime
% performance characteristics of our programs. For example, Linear Haskell\cite{}
% describes as future work an improvement to the inlining optimisation: Inlining
% is a centerpiece program optimisation primarily because of the subsequent
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
language for the Glasgow Haskell Compiler,
%ever since Linear Haskell was implemented,
both in its expressiveness to completely represent a Haskell with
linear types and in enabling more extensive compiler validations plus improved optimisations,
% it is currently impossible to enable linearity checking in Core. The reason is
linearity is effectively ignored in Core. The reason is not evidently clear:
if we can typecheck linearity in the surface level Haskell, it should also be
possible, and natural, to do so in Core.
% why do we fail to do so in Core?

The desugaring process from surface level Haskell to Core, and the subsequent
Core-to-Core optimising transformations, eliminate, and rearrange, most of the
syntactic constructs through which linearity checking is performed -- often
resulting in programs completely different from the original, especially due to
the flexibility laziness provides a compiler in the optimisations it may
perform. % without changing the program semantics.
%
Crucially, since optimisations do not destroy linearity, the resulting program
is still linear \emph{semantically}, however, the current linear type system
fails to recognize it as linear.
%
% The optimisations transform programs that are linear into ones that don't
% \emph{look} linear, but remain linear \emph{semantically}.
%
For instance, let $x$ be a linear resource in the two following programs, where
the latter results from inlining $y$ in the let body of the former. Despite the
result no longer \emph{looking} linear (as there are now two syntactic
occurrences of the linear resource $x$), the program \emph{is} indeed linear
because the let-bound expression freeing $x$ is never evaluated, so $x$ is
consumed exactly once when it is freed in the let body:
% executed, $x$ will be freed exactly once:
%
% , \emph{is} linear, as the let bound expression freeing $x$
% is never evaluated (because is not needed) -- thus $x$ is only consumed once
% when freed in the let body:
\[
\begin{array}{ccc}
\llet{y = \textsf{free}~x}{y} & \Longrightarrow_{Inlining} & \llet{y = \textsf{free}~x}{\textsf{free}~x}
\end{array}
\]

% \begin{boxedminipage}
% \begin{code}
% let y = free x
% in free x
% \end{code}
% \end{boxedminipage}

The Core optimising transformations expose a fundamental limitation of Core's
linear type system: it does not account for the call-by-need evaluation model
of Core, and thus a whole class of programs that are linear under the lens of
lazy evaluation are rejected by Core's current linear type system.

In this work, we address this limitation (and its implications on validating
and influencing optimising transformations) by designing a type system which
understands semantic linearity in the presence of laziness and is suitable for
the intermediate language of an optimising compiler.
%
In detail, our contributions are:
%
\begin{itemize}

\item We explain and provide insights into \emph{semantic} linearity in
contrast to \emph{syntactic} linearity, in Haskell, by example
($\S$~\ref{sec:linearity-semantically}).

\item We introduce Linear Core, a type system for a linear lazy language with
all key features from Core (except for type equality coercions), which,
crucially, understands semantic linearity in the presence of laziness. To the
best of our knowledge, this is the first type system to understand linearity
semantically in the context of lazy evaluation
($\S$~\ref{sec:main:linear-core}).

\item We prove Linear Core to be sound (well-typed Linear Core programs do not
get \emph{stuck}) and prove that multiple optimising transformations (which
currently violate linearity in Core) preserve types and linearity in Linear
Core ($\S$~\ref{sec:main:metatheory}).

\item We implement Linear Core as a GHC plugin which typechecks linearity in
all intermediate Core programs produced during the compilation process, showing
it accepts the intermediate programs resulting from (laziness-abusing)
transformations in linearity-heavy Haskell libraries, such as
\texttt{linear-base} ($\S$~\ref{sec:discuss:implementation}).

\end{itemize}
%
We review background concepts fundamental to our work in
Chapter~\ref{sec:background}, including linear type systems, linear types in
Haskell, evaluation strategies, Core's type system, and multiple optimising
transformations applied by GHC in its compilation process.
%
We compare our contributions to related work and discuss possible
avenues for further research (highlighting so-called \emph{multiplicity
coercions}) in Chapter~\ref{sec:discussion}, which concludes the document.


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

% \todo[inline]{Glimpse at how core optimisations can get us into these situations where we have to see this linearity}

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
% transformation is applied; WIP Proofs of optimisations
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
\bibliographystyle{plainyr}
\bibliography{references}
\end{SingleSpace}

\appendix

\chapter{Type Safety Proofs}

\section{Type Preservation\label{sec:proof:type-preservation}}

\input{language-v4/proofs/TypePreservationTheorem}

\section{Progress\label{sec:proof:progress}}

\input{language-v4/proofs/ProgressTheorem}

\section{Irrelevance\label{sec:proof:irrelevance}}

\input{language-v4/proofs/WHNFConvSoundness}

\section{Substitution Lemmas\label{sec:proof:substitution-lemmas}}

\input{language-v4/proofs/LinearSubstitutionLemma}

\input{language-v4/proofs/UnrestrictedSubstitutionLemma}

\input{language-v4/proofs/DeltaSubstitutionLemma}

\chapter{Optimisations preserve linearity}

Proofs are given inline in Chapter~\ref{sec:optimisations-preserve-types-meta},
with the exception of the proof that \emph{case-of-case} preserves types, which
is lengthier than the others.

\section{Case of Case\label{sec:proof:caseofcase}}

\input{language-v4/proofs/optimizations/CaseOfCase}


% Already given inline
% \section{Assumptions}

% \input{language-v4/proofs/DeltaLinearLemma}

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

