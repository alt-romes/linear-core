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
\usecolortheme{spruce}
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

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format forall = "\forall"
%format %-> = "\multimap"
%format . = ".\;"
%format /\ = "\Lambda"
%format hlg (a) = "\colorbox{working}{\hspace{-7pt}$" a "$}"
%format hlr (a) = "\colorbox{noway}{\hspace{-7pt}$" a "$}"
%format hl (a) = "\colorbox{limitation}{\hspace{-7pt}$" a "$}"

\newcommand{\myFor}[2]{\For{$#1$}{$#2$}}
\newcommand{\id}[1]{\textsf{\textsl{#1}}}

\renewcommand{\Varid}[1]{\textcolor{Sepia}{\id{#1}}}
\renewcommand{\Conid}[1]{\textcolor{OliveGreen}{\id{#1}}}
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

% \begin{frame}{In 5 minutes ...}
% \begin{itemize}
% \item Linear Types
% \item Laziness
% \item Interaction
% \item Compiler Optimizations
% \item A Type System for Semantic Linearity?
% \end{itemize}
% \end{frame}

\begin{frame}{Lazy Evaluation}
Expressions under lazy evaluation are only \emph{evaluated} when \emph{needed}
\pause
\only<2>{
\begin{code}
f :: Ptr -> ()
f x =
  if condition
    then free x
    else free x
\end{code}
}
\only<3>{
\begin{code}
f :: Ptr -> ()
f x =
  if condition
    hl(then free x)
    else free x
\end{code}
}
\only<4-5>{
\begin{code}
f :: Ptr -> ()
f x =
  hl(let y = free x)
  if condition
    hl(then y)
    else free x
\end{code}
}
% An imperative programmer will throw his hands on his head: oh dear.
% but all is fine
\only<5>{
\begin{itemize}
\item We always |free x| \emph{exactly once}, because |y| is only evaluated when the |condition| is true.
\end{itemize}
}
\end{frame}

\begin{frame}{And Linear Types}
A linear function ($\lolli$) consumes its argument \emph{exactly once}
\pause
\begin{minipage}{0.45\textwidth}
\begin{code}
add1 :: Int %-> Int
add1 x = x + 1
\end{code}
\end{minipage}
\pause
\begin{minipage}{0.45\textwidth}
\begin{code}
dup :: Int %-> (Int,Int)
dup x = (x,x)
\end{code}
\end{minipage}
% Dizer como isto são exemplos pouco interessantes, mas linear types permitem
% escrever resource-safe abstractions (resources like pointers or file handles)
\end{frame}

% \begin{frame}{And Linear Types}
% \begin{code}
% add1 :: Int %-> Int
% add1 x = x + 1
% \end{code}
% \pause
% \begin{code}
% madd1 :: Bool -> Int %-> Int
% madd1 condition x =
%   if condition
%     then add1 x
%     else x
% \end{code}
% \end{frame}

\begin{frame}{Which is aggressively optimized}

% Because of laziness we can do much more.
% Linearity would also allow us to improve certain optimizations, because if we
% know something to be used exactly once we can e.g. avoid heap allocations

%\begin{tikzpicture}[node distance=2cm]
%\node (haskell-code) [is] {Haskell Code};
%\node (dothings) [do, below of=haskell-code] {Elaborate};
%\node (elaborated-haskell) [is, below of=dothings] {Elaborated Haskell};
%\node (desugar) [do, below of=elaborated-haskell] {Desugar};
%\node (core) [is, right of=desugar] {Core};
%\node (opt) [do, right of=core] {Optimise};
%\node (gen-code) [do, below of=core] {Generate Code};
%\node (machinecode) [is,below of=opt] {Machine Code};
%\draw [arrow] (haskell-code) -- (dothings);
%\draw [arrow] (dothings) -- (elaborated-haskell);
%\draw [arrow] (elaborated-haskell) -- (desugar);
%\draw [arrow] (desugar) -- (core);
%\draw [arrow] (core) -- (opt);
%\draw [arrow] (opt) -- (core);
%\draw [arrow] (core) -- (gen-code);
%\draw [arrow] (gen-code) -- (machinecode);
%\end{tikzpicture}
\centering
\begin{tikzpicture}[node distance={5cm}, thick, main/.style = {draw, rectangle, minimum size=1.5em}] 
\node[main] (1) {Haskell}; 
\pause
\node[main] (2) [right of=1] {Core};
\draw[->] (1) -- node[above] {Desugar} (2);
\pause
\draw[->] (2) to [out=225,in=315,looseness=10] node[below] {Optimize} (2);
\pause
\node[main] (3) [right of=2] {Assembly};
\draw[->] (2) -- node[above] {Code Gen} (3);

\end{tikzpicture} 
\end{frame}

\begin{frame}{Hwvr, optimizations push linearity x laziness too far}
\begin{itemize}
\item Optimizations move things around\pause
\item And programs stop \emph{looking} linear
\end{itemize}
\end{frame}

\begin{frame}{Example program that is not \emph{obviously linear}}
\begin{code}
madd1 :: Bool -> Int %-> Int
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
