\documentclass[14pt,aspectratio=169,dvipsnames]{beamer}

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


\usetheme{Copenhagen}
%\usetheme{Singapore}
\usecolortheme{seahorse}
\setbeamertemplate{navigation symbols}{}
\setbeamertemplate{itemize items}[circle]
% \setbeamercovered{transparent}
\setbeamertemplate{footline}[frame number]
\usepackage{appendixnumberbeamer}
% \setbeameroption{show notes on second screen}
% \setbeameroption{show notes}

%%%%%%%%%%%%%%  Color-related things   %%%%%%%%%%%%%%
%include polycode.fmt

%%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
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

\setbeamercolor{block body}{bg=notyet}

\title{Type-checking Linearity in Core:\\ Semantic Linearity for a Lazy Optimising Compiler}
\author{Rodrigo Mesquita\\Advisor: Bernardo Toninho}
\institute{
% NOVA School of Science and Technology
% \\
\includegraphics[width=0.4\linewidth]{../logo_nova.png}
}
\date{ }

\begin{document}

\frame{\titlepage}

\begin{frame}{Linear Haskell}
% Linear types were retroffited to Haskell by introducing linearity in the function type
Haskell has Linear Types!\\
\pause
A linear function $\lolli$ consumes its argument \emph{exactly once}
\begin{columns}
\pause
\begin{column}{0.5\textwidth}
\begin{alertblock}{}
\begin{code}
bad :: Ptr ?-> IO ()
bad x = do
  free x
  free x
\end{code}
\end{alertblock}
\end{column}
\pause
\begin{column}{0.5\textwidth}
\begin{exampleblock}{}
\begin{code}
ok :: Ptr ?-> IO ()
ok x = free x
\end{code}
\end{exampleblock}
\end{column}
\end{columns}
\end{frame}

\begin{frame}{Linearity in GHC}
\begin{center}
\begin{tikzpicture}[node distance={5cm}, thick, main/.style = {draw, rectangle, minimum size=1.5em}] 
\node[main] (1) {{\only<6->{Linear }Haskell}}; 
\pause
\node[main] (2) [right of=1] {{\only<7->{Linear }Core}};
\draw[->] (1) -- node[above] {Desugar} (2);
\pause
\draw[->] (2) to [out=225,in=315,looseness=10] node[below] {Optimize} (2);
\pause
\node[main] (3) [right of=2] {Assembly};
\draw[->] (2) -- node[above] {Code Gen} (3);
\end{tikzpicture} 
\end{center}
\onslide<5->{Core is both lazy and \only<8->{\emph{linearly} }typed}
\end{frame}

\begin{frame}{Rather, Core \emph{should be} linear...}
\begin{itemize}
\item To fully represent \emph{Linear} Haskell
\item To validate that optimisations preserve linearity
\item To possibly inform certain optimisations
% but also for consistency, uniformity with the implementation of the source language...
\end{itemize}
\end{frame}

\begin{frame}{So, why isn't Core linear?}
Optimisations heavily transform linear programs to the point they stop \emph{looking} linear
\pause
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
\pause
Linearity checking is effectively disabled because most programs would be rejected otherwise
\end{frame}

\begin{frame}{Core programs stop \emph{looking} linear}
\begin{columns}
\begin{column}{0.5\textwidth}
\begin{block}{}
\begin{code}
let y = free ptr
in if condition
  then y
  else return ptr
\end{code}
\end{block}
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
\end{frame}

\begin{frame}{Semantic vs Syntactic Linearity}

\begin{itemize}
\item Programs are still linear \emph{semantically} because of laziness, but are rejected by the type system\pause
\item \textbf{Key insight:} Under lazy evaluation,\\
  \begin{center}
  \emph{syntactic} occurrence $\nRightarrow$ \emph{consuming} a resource\\
  \emph{syntactic} linearity $\neq$ \emph{semantic} linearity
  \end{center}\pause
  % Under call-by-value the distinction barely exists
  % This is a problem unique to Haskell
\item We type \emph{syntactic} linearity in Core, but that is not enough\pause
\item Optimisations push interaction between laziness and linearity to the limit
\end{itemize}

% The meaning of \emph{consuming} a resource is conflated with its
% \emph{syntactic} occurrence... and that becomes a problem under \emph{lazy} evaluation!

% Under lazy evaluation, a syntactic occurrence of a linear resource is not necessarily \emph{consuming} it.
% We call 
\end{frame}


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

\begin{frame}{Our Contributions}
\begin{itemize}
% \item We describe \emph{semantic} linearity under lazy evaluation
\item Linear Core: a type system that \colorbox{notyet}{understands} semantic linearity in the presence of laziness
% Must mention that yellow box means our type system accepts
\item We proved Linear Core and multiple optimising transformations to be sound
\item We implemented Linear Core as a GHC plugin
\end{itemize}
\end{frame}


% \begin{frame}{In 5 minutes ...}
% \begin{itemize}
% \item Linear Types
% \item Laziness
% \item Interaction
% \item Compiler Optimizations
% \item A Type System for Semantic Linearity?
% \end{itemize}
% \end{frame}

\begin{frame}{Lazy evaluation}
Expressions under lazy evaluation are only \emph{evaluated} when \emph{needed}
\pause
\begin{code}
f :: Ptr -> ()
f x =
  if condition
    hli(then free x)
    else free x
\end{code}
\end{frame}

\begin{frame}{Lazy evaluation}
Expressions under lazy evaluation are only \emph{evaluated} when \emph{needed}
\begin{code}
f :: Ptr -> ()
f x =
  hli(let y = free x in)
  if condition
    hli(then y)
    hli(else free x)
\end{code}
\pause
% An imperative programmer will throw his hands on his head: oh dear.
% but all is fine
\only<5>{We always |free x| \emph{exactly once}, because |y| is only evaluated when the |condition| is true.}
\only<6>{Laziness keeps us pure and allows the compiler to do more} %infinite data structures$\dots$}
% Dizer porque é que laziness interessa
\end{frame}


\begin{frame}{and linear types}
A linear function ($\lolli$) consumes its argument \emph{exactly once}
\pause
\begin{minipage}{0.45\textwidth}
\begin{code}
id :: Int ?-> Int
id x = x
\end{code}
\end{minipage}
\pause
\begin{minipage}{0.45\textwidth}
\begin{code}
hlin(dup :: Int ?-> (Int,Int))
dup x = (x,x)
\end{code}
\end{minipage}
% Dizer como isto são exemplos pouco interessantes, mas linear types permitem
% escrever resource-safe abstractions (resources like pointers or file handles)
\pause
Linearly typed abstractions can guarantee correct resource usage
\end{frame}

% \begin{frame}{And Linear Types}
% \begin{code}
% add1 :: Int ?-> Int
% add1 x = x + 1
% \end{code}
% \pause
% \begin{code}
% madd1 :: Bool -> Int ?-> Int
% madd1 condition x =
%   if condition
%     then add x
%     else x
% \end{code}
% \end{frame}

\begin{frame}{... interact non-trivially}
How do we type linearity in the presence of laziness?
\begin{code}
hlin(f :: Ptr ?-> ())
f x =
  if condition
    hli(then free x)
    hli(else free x)
\end{code}
\end{frame}

\begin{frame}{... interact non-trivially}
How do we type linearity in the presence of laziness?
\begin{code}
f :: Ptr ?-> ()
f x =
  hli(let y = free x)
  if condition
    hli(then y)
    hli(else free x)
\end{code}
\pause
\only<-6>{
Under lazy evaluation, $x$ is always used \emph{exactly once} when the program is run \pause -- $x$ is used linearly!
}
\only<7>{
However, this program, is \textcolor{red}{rejected} by linear type systems!
}
\end{frame}

\begin{frame}{Linearity in Haskell}

Linear typing that accounts for lazy evaluation has not been previously considered
  \begin{itemize}
  \item<2-> Typing is usually not concerned with evaluation.
  \item<3-> Linearity is different,
  \item<4-> but only wrt lazy evaluation.
  \end{itemize}
\pause
\onslide<5->{
Haskell has both linear types and lazy evaluation
  \begin{itemize}
  \item<6-> Linearity is typed conservatively.
  \item<7-> GHC's intermediate language is typed,
  \item<8-> and heavily transformed by (ab)using laziness.
  \end{itemize}
}

\end{frame}

\begin{frame}{}

There is a mismatch between linear programs and programs accepted as linear

\begin{itemize}
\item<1-> 
\end{itemize}

\end{frame}

\begin{frame}
Aproveitar aquele slide do Simon
\end{frame}

\begin{frame}{Definition of consuming $x$ once}

The Linear Haskell definition of \emph{consume exactly once}:
\begin{itemize}
\item To consume a value of atomic base type (like Int or Ptr) exactly once, just evaluate it.
\item To consume a function value exactly once, apply it to one argument, and consume its result exactly once.
\item To consume a pair exactly once, pattern-match on it, and consume each component exactly once.
\end{itemize}

\end{frame}

\begin{frame}{Hwvr, optimizations push linearity x laziness too far}
\begin{itemize}
\item Optimizations move things around\pause
\item And programs stop \emph{looking} linear
\end{itemize}
\end{frame}

\begin{frame}{Example program that is not \emph{obviously linear}}
\begin{code}
madd1 :: Bool -> Int ?-> Int
madd1 condition x =
  let y = add1 x
  if condition
    then y
    else x
\end{code}
\end{frame}

\begin{frame}{Motivation: The short story}
\begin{itemize}
% \item Core's current linearity is violated after optimizations\pause
% \item The compiler doesn't duplicate/forget linear resources\pause
\item Core's \emph{type system} does not understand linearity x laziness\pause
\item So it cannot use linearity for optimizations\pause
\item Neither validate linearity internally
\end{itemize}
\end{frame}

\begin{frame}{Our contributions}
\begin{itemize}
\item We developed a \emph{type system} that understands linearity x laziness\pause
\item Validating that optimisations preserve linearity\pause
\item And implemented it as a GHC plugin
\end{itemize}
\end{frame}

\begin{frame}{ }
\centering \emph{Fim}
\end{frame}

\appendix

\begin{frame}{System FC}

\only<1-2>{
\begin{itemize}
\item<1-> $System~F_C$ is a polymorphic lambda calculus with explicit type-equality coercions
\item<2-> A coercion $\sigma_1\sim\sigma_2$ can be used to safely
\emph{cast} an expression $e$ of type $\sigma_1$ to type $\sigma_2$,
written $e\blacktriangleright\sigma_1\sim\sigma_2$.
% Coercions are crucial to express a lot of surface Haskell features, such as
% GADTs, type families and newtypes
\end{itemize}
}

\only<3>{
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


%% Proofs and rules
\input{../../proof}
\input{../../language-v2/proof}
\input{../../language-v3/proof}
\input{../../language-v4/proof}
\input{../../language-v4/Syntax}
\input{../../language-v4/TypingRules}

\begin{frame}{Sample: $\Delta$-bound variables}
\small
\[
\begin{array}{c}
\TypeVarDelta\\
\\\pause
\TypeLet
\end{array}
\]
\end{frame}

\end{document}

% vim: foldmarker=\\begin{frame},\\end{frame} foldenable
