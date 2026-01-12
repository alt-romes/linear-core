\documentclass[14pt,aspectratio=169,dvipsnames]{beamer}

\usepackage{soul}
\usepackage{tabularx}
\usepackage{booktabs}
\usepackage{makecell}
\usepackage{amsmath}
\usepackage{mathtools}
\usepackage{xargs}
\usepackage{amssymb}
\usepackage{cleveref}
\usepackage{cmll}
\usepackage{fancyvrb}
\usepackage{mathpartir}
\usepackage{todonotes}
\usepackage{mdframed}

\newcommand{\bang}{{!}}
\newcommand{\lolli}{\multimap}
\newcommand{\one}{\mathbf{1}}
\newcommand{\parawith}[1]{\paragraph{\emph{#1}}}
\newcommand{\tensor}{\otimes}

\newcommand{\ccase}[2]{\mathsf{case}~#1~\mathsf{of}~#2}
\newcommand{\lletrec}[2]{\mathsf{letrec}~#1~\mathsf{in}~#2}
\newcommand{\llet}[2]{\mathsf{let}~#1~\mathsf{in}~#2}

\usetheme{welltyped}
%\usetheme{Singapore}
%\usecolortheme{seahorse}
\setbeamertemplate{navigation symbols}{}
\setbeamertemplate{itemize items}[circle]
% \setbeamercovered{transparent}
\setbeamertemplate{footline}{
  \hfill%
  \usebeamercolor[fg]{page number in head/foot}%
  \usebeamerfont{page number in head/foot}%
  \setbeamertemplate{page number in head/foot}[framenumber]%
  \usebeamertemplate*{page number in head/foot}\kern1em\vskip2pt%
}
\usepackage{appendixnumberbeamer}
% \setbeameroption{show notes on second screen}
% \setbeameroption{show notes}

%%%%%%%%%%%%%%  Color-related things   %%%%%%%%%%%%%%
%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{" a "}"
%format ==> = "\Longrightarrow"
%format forall = "\forall"
%format ?-> = "\multimap"
%format . = ".\;"
%format /\ = "\Lambda"
%format hlg (a) = "\colorbox{working}{\hspace{-7pt}$" a "$}"
%format hl (a) = "\colorbox{limitation}{\hspace{-7pt}$" a "$}"
%format hln (a) = "\colorbox{limitation}{\hspace{-3pt}$" a "$}"

%% Used:
%format hli (a) = "\textcolor<+(1)>{red}{\hspace{-4pt}" a "}"
%format hlr (a) = "\textcolor{red}{\hspace{-4pt}" a "}"
%format hlin (a) = "\textcolor<+(1)>{red}{" a "}"

%format boldPtr = "\textbf{ptr}"
%%%%%%%%%%%%  End of Color-related things   %%%%%%%%%%%%

% It might make sense to add pretty formating of individual things
% like "forall", cf.
% https://github.com/goldfirere/thesis/blob/master/tex/rae.fmt

% colorboxes, from rae's thesis as well
\definecolor{working}{rgb}{0.9,1,0.9}
\newmdenv[hidealllines=true,backgroundcolor=working,innerleftmargin=-3pt,innerrightmargin=-3pt,innertopmargin=-3pt,innerbottommargin=-3pt,skipabove=3pt,skipbelow=3pt]{working}
\newcommand{\workingcolorname}{light green}

\definecolor{notyet}{rgb}{1,1,0.85}
\newmdenv[hidealllines=true,backgroundcolor=notyet,innerleftmargin=-3pt,innerrightmargin=-3pt,innertopmargin=-3pt,innerbottommargin=-3pt,skipabove=3pt,skipbelow=3pt]{notyet}
\newcommand{\notyetcolorname}{light yellow}

\definecolor{noway}{rgb}{1,0.9,0.9}
\newmdenv[hidealllines=true,backgroundcolor=noway,innerleftmargin=-7pt,innerrightmargin=-7pt,innertopmargin=-3pt,innerbottommargin=-3pt,skipabove=3pt,skipbelow=3pt]{noway}
\newcommand{\nowaycolorname}{light red}

\definecolor{limitation}{rgb}{1.0, 0.875, 0.75}
\newmdenv[hidealllines=true,backgroundcolor=limitation,innerleftmargin=0pt,innerrightmargin=0pt,innertopmargin=-3pt,innerbottommargin=-3pt,skipabove=3pt,skipbelow=3pt]{limitation}
\newcommand{\limitationcolorname}{light orange}

\usepackage[utf8]{inputenc}

\usepackage{tikz}
\usetikzlibrary{shapes.geometric, arrows}
\tikzstyle{is} = [rectangle, minimum width=3cm, minimum height=1cm, text centered, draw=black, fill=orange!30]
\tikzstyle{do} = [trapezium, trapezium left angle=70, trapezium right angle=110, minimum width=3cm, minimum height=1cm, text centered, draw=black, fill=blue!30]
\tikzstyle{arrow} = [thick,->,>=stealth]

\AtBeginDocument{%
  \setbeamercolor{block body}{parent=,use=,fg=black,bg=notyet}
  \setbeamercolor{block body alerted}{parent=,use=,fg=black,bg=noway}
  \setbeamercolor{block body example}{parent=,use=,fg=black,bg=working}
}

%% Proofs and rules
\input{../../proof}
\input{../../language-v2/proof}
\input{../../language-v3/proof}
\input{../../language-v4/proof}
\input{../../language-v4/Syntax}
\input{../../language-v4/TypingRules}

\title{Lazy Linearity for a Core Functional Language}
\author[R. Mesquita \& B. Toninho]{%
  Rodrigo Mesquita\inst{1} \and
  Bernardo Toninho\inst{2,3}
}

\institute{%
  \inst{1} Well-Typed LLP, London, United Kingdom\\
  \inst{2} Instituto Superior Técnico, University of Lisbon, Lisbon, Portugal\\
  \inst{3} INESC-ID, Lisbon, Portugal\\
}
\date{ }

\begin{document}

% I'll be presenting <title>, a work the studies the interaction between
% laziness and linearity in the heart of the Glasgow Haskell compiler.
\frame{\titlepage}

\begin{frame}{Linear Types}
A linear function $\lolli$ consumes its argument \emph{exactly once}
\begin{columns}
\begin{column}{0.5\textwidth}
\begin{alertblock}{}
\begin{code}
bad :: Ptr ?-> IO ()
bad ptr = do
  free ptr
  free ptr
\end{code}
\end{alertblock}
\end{column}
\begin{column}{0.5\textwidth}
\begin{exampleblock}{}
\begin{code}
ok :: Ptr ?-> IO ()
ok ptr = free ptr
\end{code}
\end{exampleblock}
\end{column}
\end{columns}
\end{frame}

\begin{frame}{Is this function linear?}
\begin{block}{}
\large
\begin{code}
interesting :: Ptr ?-> IO ()
interesting boldPtr =
  let baz = free boldPtr
  if ...
    then baz
    else free boldPtr
\end{code}
\end{block}
\end{frame}

\begin{frame}{It depends on the evaluation strategy}
\begin{minipage}{0.65\textwidth}
The |interesting| function frees |ptr|:
\begin{itemize}
\item More than once, under strict evaluation
\item Exactly once, under non-strict evaluation
\end{itemize}
\end{minipage}
\begin{minipage}{0.34\textwidth}
\begin{code}
let baz = free ptr
if ...
    then baz
    else free ptr
\end{code}
\end{minipage}

\end{frame}


\begin{frame}{Yet, |interesting| is always rejected!}
All linear type systems we know of reject |interesting|.

\begin{itemize}
\item Traditional linearity is too syntactic
\item Lazy semantics of linearity are rejected
\end{itemize}
\pause
\textbf{Key observation}: \emph{syntactic linearity $\neq$ semantic linearity}
% This talk: how to accept more non-strict programs as linear
\end{frame}

% Linear Types were implemented as an extension in the Glasgow Haskell
% compiler, which is the de-facto Haskell compiler.
%
%
% Haskell is desugared to an intermediate language called Core, which is
% transformed over and over by multiple the so-called Core-to-Core
% optimisations until ultimately we generate assembly code from it.
%
% It is important to note Core is both lazy and typed, and that this allows it to fully represent Haskell.
% For one, Core is lazily evaluated like Haskell, and the desugaring and
% optimisation passes preserve types.  It is crucial in GHC that Core is typed
% because it serves as a sanity check over the correctness of source
% transformations and their implementation.
%
% With the introduction of Linear Types, we now have that Linear Haskell
% desugars to what we would call Linear Core, i.e. Core with linear types.
% Ideally, Linear Core is both lazy and linearly typed. Core being linearly
% typed benefits us like Core being typed does. We can easily validate that the
% optimising passes preserve linearity -- which should be true -- by
% typechecking linearity after every transformation! Optimiser should
% definitely not destroy linearity. We also need linearity in Core to fully represent Linear Haskell.
%%% \begin{frame}{Why do we care? Linearity in GHC}
%%% \begin{center}
%%% \begin{tikzpicture}[node distance={5cm}, thick, main/.style = {draw, rectangle, minimum size=1.5em}]
%%% \node[main] (1) {Linear Haskell};
%%% \node[main] (2) [right of=1] {{Core}};
%%% \draw[->] (1) -- node[above] {Desugar} (2);
%%% \draw[->] (2) to [out=225,in=315,looseness=10] node[below] {Optimize} (2);
%%% \node[main] (3) [right of=2] {Assembly};
%%% \draw[->] (2) -- node[above] {Code Gen} (3);
%%% \end{tikzpicture}
%%% \end{center}
%%% Core is both lazy and statically typed, but linearity has to be ignored.
%%% \end{frame}

\begin{frame}{So what?..... ATODO}
\begin{center}
\begin{tikzpicture}[node distance={5cm}, thick, main/.style = {draw, rectangle, minimum size=1.5em}]
\node[main] (1) {Linear Haskell};
\node[main] (2) [right of=1] {{Core}};
\draw[->] (1) -- node[above] {Desugar} (2);
\draw[->] (2) to [out=225,in=315,looseness=10] node[below] {Optimize} (2);
\node[main] (3) [right of=2] {Assembly};
\draw[->] (2) -- node[above] {Code Gen} (3);
\end{tikzpicture}
\end{center}
Core is lazy and typed, but linearity is ignored.
\begin{itemize}
\item Can't do sanity checking!
\item Can't use linearity for optimisations
\end{itemize}
\end{frame}

% So, why isn't Core linear? It's key to understand that the optimiser does
% not destroy linearity semantically, however, the optimised programs stop
% looking linear -- the type system no longer accepts these programs, but if
% reason about linearity semantically we can see they remain linear.
%
% Here's an example, <read example>...
%
% That leaves us at: Linearity is currently ignored in Core. The alternative
% would be to reject most linear programs after they are optimised, even though
% they are correct and it is only a type system limitation that we are not able
% to say they are in the intermediate language's type system.
% And this only comes up in Core because the optimiser changes around things
% that were previously linearly conservatively.
\begin{frame}{Why is linearity dropped in GHC Core?}
% Optimisations heavily transform linear programs to the point they stop \emph{looking} linear
Optimizations destroy \emph{syntactic} linearity
% \begin{column}{0.5\textwidth}
% \begin{block}{}
% \begin{code}
% myFree :: Ptr ?-> IO ()
% myFree x = do
%   let y = free x
%   free x
% \end{code}
% \end{block}
% \end{column}
% \pause
\begin{block}{}
\centering
\begin{code}
let y = free x in y
==>
let y = free x in free x
\end{code}
\end{block}
%Linearity is ignored, or too many programs would be rejected
\end{frame}

%% Summarising,
%% <bullets>
%\begin{frame}{Semantic vs Syntactic Linearity}
%
%\begin{itemize}
%\item Programs are still linear \emph{semantically} because of laziness\pause
%      %, but are rejected by the type system\pause
%\item \textbf{Key insight:} Under lazy evaluation,\\
%  \begin{center}
%  \emph{syntactic} occurrence $\nRightarrow$ \emph{consuming} a resource\\
%  \emph{syntactic} linearity $\neq$ \emph{semantic} linearity
%  \end{center}\pause
%  % Under call-by-value the distinction barely exists
%  % This is a problem unique to Haskell
%\item We type \emph{syntactic} linearity in Core, but that is not enough\pause
%\item Optimisations push laziness x linearity to the limit
%\end{itemize}
%
%% The meaning of \emph{consuming} a resource is conflated with its
%% \emph{syntactic} occurrence... and that becomes a problem under \emph{lazy} evaluation!
%
%% Under lazy evaluation, a syntactic occurrence of a linear resource is not necessarily \emph{consuming} it.
%% We call 
%\end{frame}

%\begin{frame}{Which is aggressively optimized}

%% Because of laziness we can do much more.
%% Linearity would also allow us to improve certain optimizations, because if we
%% know something to be used exactly once we can e.g. avoid heap allocations

%%\begin{tikzpicture}[node distance=2cm]
%%\node (haskell-code) [is] {Haskell Code};
%%\node (dothings) [do, below of=haskell-code] {Elaborate};
%%\node (elaborated-haskell) [is, below of=dothings] {Elaborated Haskell};
%%\node (desugar) [do, below of=elaborated-haskell] {Desugar};
%%\node (core) [is, right of=desugar] {Core};
%%\node (opt) [do, right of=core] {Optimise};
%%\node (gen-code) [do, below of=core] {Generate Code};
%%\node (machinecode) [is,below of=opt] {Machine Code};
%%\draw [arrow] (haskell-code) -- (dothings);
%%\draw [arrow] (dothings) -- (elaborated-haskell);
%%\draw [arrow] (elaborated-haskell) -- (desugar);
%%\draw [arrow] (desugar) -- (core);
%%\draw [arrow] (core) -- (opt);
%%\draw [arrow] (opt) -- (core);
%%\draw [arrow] (core) -- (gen-code);
%%\draw [arrow] (gen-code) -- (machinecode);
%%\end{tikzpicture}
%\centering
%\begin{tikzpicture}[node distance={5cm}, thick, main/.style = {draw, rectangle, minimum size=1.5em}] 
%\node[main] (1) {Haskell}; 
%\pause
%\node[main] (2) [right of=1] {Core};
%\draw[->] (1) -- node[above] {Desugar} (2);
%\pause
%\draw[->] (2) to [out=225,in=315,looseness=10] node[below] {Optimize} (2);
%\pause
%\node[main] (3) [right of=2] {Assembly};
%\draw[->] (2) -- node[above] {Code Gen} (3);

%\end{tikzpicture} 
%\end{frame}

% Our contributions...
% <bullets>
% Must mention that yellow box means our type system accepts...
\begin{frame}{Our Contributions}
\begin{itemize}
% \item We describe \emph{semantic} linearity under lazy evaluation
\item Type system which \colorbox{notyet}{accepts} the lazy semantics of linearity statically
\item Soundness proof, guaranteeing runtime linearity
\item Prototype as GHC plugin
\end{itemize}
\end{frame}

% Let's talk about ...
\begin{frame}{}
\centering
\large
Lazy Linearity, by example
\end{frame}

\begin{frame}{Lazy Linearity: Lets}
\begin{block}{}
\begin{code}
let y = free ptr
in if condition
  then y
  else return ptr
\end{code}
\end{block}

Resources in lets are only consumed if the binder is evaluated
\end{frame}

\begin{frame}{Lazy Linearity: Case}
% Estes programas são criados por optimizações, apesar de parecerem programas
% que um programador nunca escreveria
\begin{columns}
\begin{column}{0.5\textwidth}
\begin{exampleblock}{}
\begin{code}
case (x,y) of
  (a, b) -> something a b
\end{code}
\end{exampleblock}
\end{column}
\pause
\begin{column}{0.5\textwidth}
\begin{block}{}
\begin{code}
case (x,y) of
  (a, b) -> something x y
\end{code}
\end{block}
\end{column}
\end{columns}
\pause
\begin{columns}
\begin{column}{0.5\textwidth}
\begin{alertblock}{}
\begin{code}
case free x of
  Result v -> free x
\end{code}
\end{alertblock}
\end{column}
\pause
\begin{column}{0.5\textwidth}
\begin{alertblock}{}
\begin{code}
case use x of
  Result v -> ()
\end{code}
\end{alertblock}
\end{column}
\end{columns}
\pause
Case expressions drive evaluation, consuming (parts of) resources
% (scrutinee is \emph{not} in WHNF)
\end{frame}

\begin{frame}{}
\centering
\large
Linear Core
\end{frame}

%\begin{frame}{Linear Core: $Let$-vars}
%\begin{columns}
%\begin{column}{0.5\textwidth}
%\begin{block}{}
%%format yWithUEPtr = y "_{\{ptr\}}"
%\begin{code}
%let yWithUEPtr = free ptr in yWithUEPtr
%\end{code}
%\end{block}
%\end{column}
%\pause
%\begin{column}{0.5\textwidth}
%\[
%\TypeVarDelta
%\]
%\end{column}
%\end{columns}
%\pause
%\vspace{0.5cm}
%$Let$-binder bodies don't consume resources\pause
%\begin{itemize}
%\item Annotate Let-vars with linear resources $\D$ used in its body\\\pause
%\item Using a Let-var entails using all of its $\D$
%\end{itemize}
%\end{frame}

\begin{frame}{Linear Core: Lets}
\begin{block}{}
%format yWithUEPtr = y "_{\{ptr\}}"
\begin{code}
let yWithUEPtr = free ptr
in if condition
  then yWithUEPtr
  else return ptr
\end{code}
\end{block}

%% \[
%% \onslide<3->{
%% \infer
%% {
%% \onslide<4->{\cdot ; ptr \vdash free~ptr}\\
%% \onslide<5->{y{:}_{\{ptr\}}; ptr \vdash |if condition| \dots}
%% }
%% {\cdot; ptr \vdash \llet{y = free~ptr}{\dots}}
%% }
%% \]

\textbf{Key idea:} $Let$-binding doesn't consume resources
\begin{itemize}
\item Annotate $let$-vars with resources used in its body
\item Using $let$-vars consumes annotated context
\end{itemize}
\end{frame}

\begin{frame}{Lets in Linear Haskell (Standard)}
\[
\infer
{
{\Gamma ; \Delta_1 \vdash e_1}\\
{\Gamma; \Delta_2, y \vdash e_2}
}
{\Gamma; \Delta_1, \Delta_2 \vdash \llet{y = e_1}{e_2}}
\]
\end{frame}

\begin{frame}{Lets in Linear Core}
\[
\infer
{
{\Gamma ; \Delta_1 \vdash e_1}\\
{\Gamma, y{:}_{\Delta_1}; \Delta_1, \Delta_2 \vdash e_2}
}
{\Gamma; \Delta_1, \Delta_2 \vdash \llet{y = e_1}{e_2}}
\]
\end{frame}

\begin{frame}{$\Delta$-Vars in Linear Core}
\[
\infer
{
{\Delta_1 = \Delta_2}
}
{\Gamma, y{:}_{\Delta_1}; \Delta_2 \vdash y}
\]
\end{frame}

\begin{frame}{Linear Core: Case}
Case scrut evaluate to WHNF, unless they are already in WHNF
% Recalling the key idea that if it is already in WHNF no EVALUATION happens, thus no resources are consumed (thuis can be in the next slide)
\begin{columns}
\begin{column}{0.5\textwidth}
\begin{block}{}
\begin{code}
case (x,y) of
  (a, b) -> something x y
\end{code}
\end{block}
\end{column}
\begin{column}{0.5\textwidth}
\begin{alertblock}{}
\begin{code}
case free x of
  Result v -> free x
\end{code}
\end{alertblock}
\end{column}
\end{columns}
\vspace{0.5cm}
\textbf{Key idea:} We need to branch on \emph{WHNF-ness}
% Não explico os detalhes na apresentação, mas que conseguimos tratar no
% sistema na sua forma mais geral
\end{frame}

\begin{frame}{Linear Core: Case WHNF}
%format aWithUEX = a "_{\{x\}}"
%format bWithUEY = b "_{\{y\}}"
\begin{columns}
\begin{column}{0.5\textwidth}
\begin{block}{}
\begin{code}
case (x,y) of
  (aWithUEX, bWithUEY) -> use x y
\end{code}
\end{block}
\end{column}
\pause
\begin{column}{0.5\textwidth}
\[
\onslide<3->{
\infer
{
\onslide<4->{\cdot; x, y \vdash (x,y)}\\
\onslide<5->{a{:}_{\{x\}}, b{:}_{\{y\}}; x,y \vdash use~x~y}
}
{
\cdot; x,y \vdash \ccase{(x,y)}{(a,b) \to\dots}
}
}
\]
\end{column}
\end{columns}
\vspace{0.5cm}

\onslide<2->{
\begin{itemize}
\item Scrutinee resources are available in the body\\
\item Pattern variables are annotated with corresponding scrutinee variables
\end{itemize}
}
\end{frame}

\begin{frame}{Linear Core: Case Not-WHNF}
%format vWithIrrX = v "_{\{[x]\}}"
\begin{columns}
\begin{column}{0.5\textwidth}
\begin{alertblock}{}
\begin{code}
case free x of
  Result vWithIrrX -> free x
\end{code}
\end{alertblock}
\end{column}
\begin{column}{0.5\textwidth}
\[
\onslide<3->{
\infer
{
\onslide<4->{\cdot; x \vdash free~x}\\
\onslide<5->{v{:}_{\{[x]\}}; [x] \vdash free~x}
}
{
\cdot; x \vdash \ccase{free~x}{\dots}
}
}
\]
\end{column}
\end{columns}
\vspace{0.5cm}
\onslide<2->{
Scrutinee resources are \emph{irrelevant} in the body
\begin{itemize}
\item They cannot be instantiated with $Var$
\item But must still be used exactly once
% the only way to do this is via pattern variables
}
\end{itemize}
\end{frame}

\begin{frame}{Linear Core: Case Not-WHNF}
%format vWithIrrX = v "_{\{[x]\}}"
\begin{columns}
\begin{column}{0.5\textwidth}
\begin{alertblock}{}
\begin{code}
case free x of
  Result vWithIrrX -> ()
\end{code}
\end{alertblock}
\end{column}
\begin{column}{0.5\textwidth}
\[
\infer
{
{\cdot; x \vdash free~x}\\
{v{:}_{\{[x]\}}; [x] \vdash ()}
}
{
\cdot; x \vdash \ccase{free~x}{\dots}
}
\]
\end{column}
\end{columns}
\vspace{0.5cm}
Scrutinee resources are \emph{irrelevant} in the body
\begin{itemize}
\item They cannot be instantiated with $Var$
\item But must still be used exactly once
% the only way to do this is via pattern variables
\end{itemize}
\end{frame}

\begin{frame}{In the paper...}
\begin{itemize}
\item Metatheory:
    \begin{itemize}
    \item Soundness and linear resource usage
    \item Optimising transformations preserve linearity
    \end{itemize}
\item GHC Plugin implementing Linear Core
\end{itemize}
\end{frame}

% \begin{frame}{Metatheory: Linear Core}
% % Estranho ter esta distinção que depende do estado de algo at runtime, isto é type safe?
% % Sistema de tipos razoável
% \begin{itemize}
% \item Not obvious whether these rules make sense together
% \item We proved the system is type safe via preservation + progress
% % Auxiliary lemma Irrelevance gives us that an alternative for a scrutinee not
% % in WHNF that is well-typed with an irrelevant resource in the context is also
% % well-typed if that irrelevant resource is substituted for any linear
% % environment uniformly regardless of the scrutinee WHNF-ness
% % \item Lots of lemmas...
% \pause
% \begin{itemize}
% \item \emph{Irrelevance} lemma
% \item Linear-var substitution lemma
% \item $\Delta$-var substitution lemma
% \item Unr-var substitution lemma
% \end{itemize}
% \end{itemize}
% \end{frame}

\begin{frame}{Conclusion}
\begin{itemize}
\item Linear Core accepts more of the lazy semantics of linearity
    \begin{itemize}
    \item Not all linear programs are accepted by Linear Core
    \item Future work: Multiplicity Coercions
    \end{itemize}
\item Suitable for Lazy Linear Core language
    \begin{itemize}
    \item Optimizations provably preserve linearity
    \item Validated in practice as GHC plugin
    \item Future work: lazy features of strict linear languages
    \end{itemize}
\end{itemize}
\end{frame}

% \begin{frame}{Lazy evaluation}
% Expressions under lazy evaluation are only \emph{evaluated} when \emph{needed}
% \pause
% \begin{code}
% f :: Ptr -> ()
% f x =
%   if condition
%     hli(then free x)
%     else free x
% \end{code}
% \end{frame}

% \begin{frame}{Lazy evaluation}
% Expressions under lazy evaluation are only \emph{evaluated} when \emph{needed}
% \begin{code}
% f :: Ptr -> ()
% f x =
%   hli(let y = free x in)
%   if condition
%     hli(then y)
%     hli(else free x)
% \end{code}
% \pause
% % An imperative programmer will throw his hands on his head: oh dear.
% % but all is fine
% \only<5>{We always |free x| \emph{exactly once}, because |y| is only evaluated when the |condition| is true.}
% \only<6>{Laziness keeps us pure and allows the compiler to do more} %infinite data structures$\dots$}
% % Dizer porque é que laziness interessa
% \end{frame}

% \begin{frame}{and linear types}
% A linear function ($\lolli$) consumes its argument \emph{exactly once}
% \pause
% \begin{minipage}{0.45\textwidth}
% \begin{code}
% id :: Int ?-> Int
% id x = x
% \end{code}
% \end{minipage}
% \pause
% \begin{minipage}{0.45\textwidth}
% \begin{code}
% hlin(dup :: Int ?-> (Int,Int))
% dup x = (x,x)
% \end{code}
% \end{minipage}
% % Dizer como isto são exemplos pouco interessantes, mas linear types permitem
% % escrever resource-safe abstractions (resources like pointers or file handles)
% \pause
% Linearly typed abstractions can guarantee correct resource usage
% \end{frame}

% % \begin{frame}{And Linear Types}
% % \begin{code}
% % add1 :: Int ?-> Int
% % add1 x = x + 1
% % \end{code}
% % \pause
% % \begin{code}
% % madd1 :: Bool -> Int ?-> Int
% % madd1 condition x =
% %   if condition
% %     then add x
% %     else x
% % \end{code}
% % \end{frame}

% \begin{frame}{... interact non-trivially}
% How do we type linearity in the presence of laziness?
% \begin{code}
% hlin(f :: Ptr ?-> ())
% f x =
%   if condition
%     hli(then free x)
%     hli(else free x)
% \end{code}
% \end{frame}

% \begin{frame}{... interact non-trivially}
% How do we type linearity in the presence of laziness?
% \begin{code}
% f :: Ptr ?-> ()
% f x =
%   hli(let y = free x)
%   if condition
%     hli(then y)
%     hli(else free x)
% \end{code}
% \pause
% \only<-6>{
% Under lazy evaluation, $x$ is always used \emph{exactly once} when the program is run \pause -- $x$ is used linearly!
% }
% \only<7>{
% However, this program, is \textcolor{red}{rejected} by linear type systems!
% }
% \end{frame}

% \begin{frame}{Linearity in Haskell}

% Linear typing that accounts for lazy evaluation has not been previously considered
%   \begin{itemize}
%   \item<2-> Typing is usually not concerned with evaluation.
%   \item<3-> Linearity is different,
%   \item<4-> but only wrt lazy evaluation.
%   \end{itemize}
% \pause
% \onslide<5->{
% Haskell has both linear types and lazy evaluation
%   \begin{itemize}
%   \item<6-> Linearity is typed conservatively.
%   \item<7-> GHC's intermediate language is typed,
%   \item<8-> and heavily transformed by (ab)using laziness.
%   \end{itemize}
% }

% \end{frame}

% \begin{frame}{}

% There is a mismatch between linear programs and programs accepted as linear

% \begin{itemize}
% \item<1-> 
% \end{itemize}

% \end{frame}

% \begin{frame}
% Aproveitar aquele slide do Simon?
% \end{frame}

% \begin{frame}{Definition of consuming $x$ once}

% The Linear Haskell definition of \emph{consume exactly once}:
% \begin{itemize}
% \item To consume a value of atomic base type (like Int or Ptr) exactly once, just evaluate it.
% \item To consume a function value exactly once, apply it to one argument, and consume its result exactly once.
% \item To consume a pair exactly once, pattern-match on it, and consume each component exactly once.
% \end{itemize}

% \end{frame}

% \begin{frame}{Hwvr, optimizations push linearity x laziness too far}
% \begin{itemize}
% \item Optimizations move things around\pause
% \item And programs stop \emph{looking} linear
% \end{itemize}
% \end{frame}

% \begin{frame}{Example program that is not \emph{obviously linear}}
% \begin{code}
% madd1 :: Bool -> Int ?-> Int
% madd1 condition x =
%   let y = add1 x
%   if condition
%     then y
%     else x
% \end{code}
% \end{frame}

% \begin{frame}{Motivation: The short story}
% \begin{itemize}
% % \item Core's current linearity is violated after optimizations\pause
% % \item The compiler doesn't duplicate/forget linear resources\pause
% \item Core's \emph{type system} does not understand linearity x laziness\pause
% \item So it cannot use linearity for optimizations\pause
% \item Neither validate linearity internally
% \end{itemize}
% \end{frame}

% \begin{frame}{Our contributions}
% \begin{itemize}
% \item We developed a \emph{type system} that understands linearity x laziness\pause
% \item Validating that optimisations preserve linearity\pause
% \item And implemented it as a GHC plugin
% \end{itemize}
% \end{frame}

%\begin{frame}{ }
%\centering \emph{Fim}
%\end{frame}

\appendix

\begin{frame}{Lazy Linearity: Case of Var}
\[
\begin{array}{c}
(\lambda z.~\ccase{z}{\_ \to z})\\\pause
\Longrightarrow_{\textrm{call by name}}\\\pause
\ccase{free~x}{\_ \to free~x}\\\pause
\\
\Longrightarrow_{\textrm{call by need}}\\\pause
\llet{y = free~x}{\ccase{y}{\_ \to y}}\\
\end{array}
\]
\end{frame}

\begin{frame}{Metatheory: Optimising Transformations}
\begin{itemize}
\item Inlining
\item $\beta$-reduction
\item $\beta$-reduction with sharing
\item $\beta$-reduction for multiplicity abstractions
\item Case-of-known-constructor
\item Full laziness
\item Local transformations (three of them)
\item $\eta$-expansion
\item $\eta$-reduction
\item Binder swap
\item Reverse binder swap (contentious!)
\item Case-of-case
\end{itemize}
\end{frame}

\begin{frame}{GHC Plugin: Linear Core Implementation}
We implemented Linear Core as a GHC plugin
\scriptsize
\input{../../prototype/core-plugin-results}
\end{frame}

\begin{frame}{System FC}

\only<1>{
\begin{itemize}
\item<1> $System~F_C$ is a polymorphic lambda calculus with explicit type-equality coercions
\item<1> A coercion $\sigma_1\sim\sigma_2$ can be used to safely
\emph{cast} an expression $e$ of type $\sigma_1$ to type $\sigma_2$,
written $e\blacktriangleright\sigma_1\sim\sigma_2$.
% Coercions are crucial to express a lot of surface Haskell features, such as
% GADTs, type families and newtypes
\end{itemize}
}

\only<2>{
\begin{definition}[Syntax]
\small
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
\end{definition}
}

\end{frame}

% \begin{frame}{Sample: $\Delta$-bound variables}
% \small
% \[
% \begin{array}{c}
% \TypeVarDelta\\
% \\\pause
% \TypeLet
% \end{array}
% \]
% \end{frame}

\end{document}

% Notas:
% Saber o que preciso de dizer em cada slide

% vim: foldmarker=\\begin{frame},\\end{frame} foldenable
