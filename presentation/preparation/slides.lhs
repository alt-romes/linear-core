\documentclass[14pt,aspectratio=169,dvipsnames]{beamer}

\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{cleveref}
\usepackage{cmll}
\usepackage{fancyvrb}
\usepackage{mathpartir}
\usepackage{todonotes}

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
\setbeamercovered{transparent}
\setbeamertemplate{footline}[frame number]
% \setbeameroption{show notes on second screen}
% \setbeameroption{show notes}

%%%%%%%%%%%%%%  Color-related things   %%%%%%%%%%%%%%
%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"
%format forall = "\forall"
%format %-> = "\multimap"
%format . = ".\;"
%format /\ = "\Lambda"

\newcommand{\myFor}[2]{\For{$#1$}{$#2$}}
\newcommand{\id}[1]{\textsf{\textsl{#1}}}

\renewcommand{\Varid}[1]{\textcolor{Sepia}{\id{#1}}}
\renewcommand{\Conid}[1]{\textcolor{OliveGreen}{\id{#1}}}
%%%%%%%%%%%%  End of Color-related things   %%%%%%%%%%%%

\usepackage[utf8]{inputenc}

\title{Type-checking Linearity in Haskell's\\ Core Intermediate Language}
\author{Rodrigo Mesquita\\ Advisor: Bernardo Toninho}
\institute{
% NOVA School of Science and Technology
% \\
\includegraphics[width=0.4\linewidth]{../logo_nova.png}
}
\date{ }

\begin{document}

\begin{frame}
    \titlepage
\end{frame}

% \section{Introduction}

\begin{frame}{Haskell is desugared to Core}

\begin{itemize}
\item<1-> Haskell is a lazy functional language, with an advanced type system
% to which \emph{linear types} were introduced
\item<2-> The whole of Haskell is transformed to the minimal Core language, which
is also functional, typed and lazy
      % Which allows us to reason about the entirety of Haskell, including all the type features and laziness
% \item<3-> Core \emph{needs} linear types to completely represent Haskell
\end{itemize}
\end{frame}

\begin{frame}{Haskell is desugared to Core}
\begin{example}[Haskell vs Core]
\begin{minipage}{0.47\textwidth}
\begin{code}
null :: [a] -> Bool
null x = case x of
  [] -> True
  _  -> False
\end{code}
\end{minipage}
\begin{minipage}{0.47\textwidth}
\begin{code}
null :: forall a . [a] -> Bool
null = /\ a. \ (x :: [a]) ->
  case x of
    [] -> True
    (:) y ys -> False
\end{code}
\end{minipage}
\end{example}
\end{frame}

\begin{frame}{Core's type-checker validates GHC}
\begin{itemize}
\item<1-> Core is \emph{really} important in the design of GHC
\item<2-> Core allows us to reason about the entirety of Haskell in a much smaller language.
\item<3-> Optimization and code generation is performed on Core
\item<3-> Type-checking Core serves as an internal consistency tool
\end{itemize}
\end{frame}

\begin{frame}{Linear Types were introduced in Haskell}
\begin{itemize}
\item<1-> Haskell's type system was extended with \emph{linear types}
\item<2-> \textbf{Core also needs linear types} to completely represent Haskell
% Otherwise it isn't expressive enough to represent Haskell
\end{itemize}
\end{frame}

\begin{frame}{Linear Typing}
\begin{block}{Linear Resource}<1->
% In a linear type system,
A linear resource must be used \emph{exactly once}.
\end{block}
\only<1>{
\begin{example}[Rejected by type-system]
  \begin{code}
  let p = malloc(4);
  in free(p);
     free(p);
  \end{code}
\end{example}
}
\only<2>{
\begin{example}[Accepted by type-system]
  \begin{code}
  let p = malloc(4);
      p' = put(p,5);
  in free(p');
  \end{code}
\end{example}
}
\end{frame}

\begin{frame}{Linear Haskell}

\only<1-2>{
\begin{itemize}
\item<1-> Linear types were retroffited to Haskell by introducing linearity in the function type
    % \begin{itemize}
    % \item<2-> A multiplicity of \texttt{1} indicates a linear function ($\to_1$)
    % \item<3-> A multiplicity of \texttt{Many} indicates an unrestricted function ($\to_\omega$)
    % \end{itemize}
    % Which has good benefits such as backwards compatibility and code
    % re-use, which are very important in the context of
\item<2-> A linear function $\lolli$ must use its argument \emph{exactly once}
\item<2-> An unrestricted function $\to$ can use its argument unrestrictedly
% \begin{example}
% \begin{code}
% id :: a %1 -> a
% \end{code}
% \end{example}
\end{itemize}
}

% \only<6-8>{
% \begin{definition}[Consuming a value]
%   \begin{itemize}
%     \item<6-> To consume a value of atomic base type, just evaluate it
%     \item<7-> To consume a function exactly once, apply it, and consume the
%     result
%     \item<8-> To consume a value of an algebraic data type, pattern-match on
%     it, and consume its linear components
%   \end{itemize}
% \end{definition}
% }

\only<3>{
\begin{example}[Linear types in Haskell]
  \begin{minipage}{0.47\textwidth}
  \begin{code}
      f :: Int %-> Int
      f x = x*2
  \end{code}
  \end{minipage}
  \begin{minipage}{0.47\textwidth}
  \begin{code}
      g :: Int -> Int
      g x = x*x + 2
  \end{code}
  \end{minipage}
\end{example}
}

% \only<10>{
% \begin{example}[Multiplicity polymorphism]
% \begin{minipage}{0.47\textwidth}
% \begin{code}
% f :: (Bool %1 -> Int) -> Int
% f c = c True
% 
% g :: (Bool -> Int) -> Int
% g c = c False
% \end{code}
% \end{minipage}
% \begin{minipage}{0.47\textwidth}
% \begin{code}
% h :: Bool %m -> Int
% h x = case x of
%   False -> 0
%   True -> 1
% \end{code}
% \end{minipage}
% \end{example}
% }
\end{frame}

%Meta: Devia ler os pontos nos slides depois de concluir aquilo que tenho para
%dizer naquele slide ou dizer no início e depois explicar? parece-me que a
%primeira opção é melhor

\begin{frame}{Linear Core is incomplete}
\begin{itemize}
\item<2-> \textbf<2>{Core's linear type-checker doesn't accept most linear
    programs}
    % Optimizing transformations destroy linearity as the type-checker sees
    % it. However, we believe optimizing transformations *don't* destroy
    % linearity, it's just a limitation of the type system
\item<3-> \textbf<3>{Core's linear type-checker is disabled} because
    otherwise disabling optimizations is far worse
    % it doesn't accept transformed Core programs
    % GHC's Core type-checker is disabled because it doesn't accept Core
    % programs that undergo optimizing transformations in Core
    % and otherwise disabling optimizing transformations is not feasible.
\end{itemize}
\end{frame}

\begin{frame}{Linear Core is a worthwhile goal}

\begin{itemize}
\item<1-> A Linear Core allows us to reason about linear types in Haskell
    % \item<4-> The entirety of Haskell can be compactly expressed in Core
    % transformational approach to optimization
    % for the desugaring and optimization passes
\item<2-> Type-checking linearity in Core serves as internal consistency tool
\begin{itemize}
\item<3-> Validate Linear Haskell's implementation
\item<3-> Validate that optimizing transformations don't destroy linearity
\end{itemize}
% \item<6-> Core type-checker is much faster than Haskell
% \item<6-> Core is based on the $System~F_C$ type-system
\end{itemize}

\end{frame}


% \begin{frame}{Context}
% 
% \begin{itemize}
%     \item<1-> Static typing eliminates errors at compile time
%     \item<2-> Linear types can enforce resource usage invariants
%         % Are expressive types
%     % \item<3-> Haskell is a lazy, purely functional programming language
%     \item<3-> Linear types were \emph<3>{only recently} introduced in Haskell
%     % \item<3-> Linear types were introduced in Haskell, 31 \emph<3>{years} after Haskell's inception.
%                 % recently introduced
%                 % Which came with new challenges such as backwards compatibility, future
%                 % proofing and code re-use
% \end{itemize}
% 
% \end{frame}

% \begin{frame}{Motivation}
% \begin{itemize}
%     \item<1-> However, linear types were also introduced in \textbf<1>{Core}
%         % a typed language that serves as Haskell's main intermediate representation
%         % Core is explicitly typed
%         % Core is very important because it serves as an internal consistency
%         % tool and validation layer of the implementation
%     \item<2-> Core programs undergo a myriad of optimizing transformations
%         \note{These (core-to-core) transformations follow a modular approach, where
%         each transformation produces Core that is further used as input to
%         other transformations
%         Which might introduce lazy let bindings (through e.g. beta reduction),
%         inline definitions, move bindings around (let-floating
%         transformations)}
%     \item<3-> \textbf<3>{Core's linear type-checker doesn't accept linear
%         programs} after optimizing transformations are applied
%         % Optimizing transformations destroy linearity as the type-checker sees
%         % it. However, we believe optimizing transformations *don't* destroy
%         % linearity, it's just a limitation of the type system
%     \item<4-> \textbf<4>{Core's linear type-checker is disabled} because
%         otherwise disabling optimizations is far worse
%         % it doesn't accept transformed Core programs
%         % GHC's Core type-checker is disabled because it doesn't accept Core
%         % programs that undergo optimizing transformations in Core
%         % and otherwise disabling optimizing transformations is not feasible.
% \end{itemize}
% \end{frame}

\begin{frame}{Objectives}
\begin{itemize}
    \item<1-> Extend Core's type-system to accommodate Linear Core
        % Big distinction between syntatically valid linearity and semantically
        % valid. Transformations result in many semantically valid but
        % syntatically invalid programs, and we need to extend Core to
        % account for this semantic linearity.
    \item<2-> Validate optimizing transformations with the new type-system
    \item<3-> Implement the extensions to Core's type-system in GHC
        % , the leading Haskell compiler
\end{itemize}
\end{frame}

% \section{Background}

% {
% \begin{frame}{Linear Lambda Calculus}
% \only<1>{
% \begin{block}{Syntax}
% \vspace*{-0.5cm}
% \[
% \begin{array}{c}
%   \begin{array}{lcl}
%     A,B & ::= & T\\
%         & \mid & A \lolli B\\
%         & \mid & \bang A\\
%    \end{array}
% \quad
%   \begin{array}{lcl}
%       M,N & ::= & u\\
%         & \mid & \lambda u. M\\
%         & \mid & M~N\\
%         & \mid & \bang M \mid \llet{!u = M}{N} \\
%    \end{array}
% \end{array}
% \]
% \end{block}
% }
% \only<1->{
% \begin{block}{$\lolli$ Introduction Rule}
% \[
%     \infer*[right=($\lolli I$)]
%     {\Gamma ; \Delta , u{:}A \vdash M : B}
%     {\Gamma ; \Delta \vdash \lambda u. M : A \lolli B}
% % \quad
% %     \infer*[right=($\lolli E$)]
% %     {\Gamma ; \Delta \vdash M : A \lolli B \and \Gamma ; \Delta' \vdash N : A}
% %     {\Gamma ; \Delta, \Delta' \vdash M~N : B}
% \]
% \end{block}
% }
% \only<2>{
% \begin{example}
% \[
%     \lambda h.~\mathsf{return}~\star;
%     \qquad
%     \lambda h.~\mathsf{close}~h;~\mathsf{close}~h;
% \]
% \end{example}
% }
% \end{frame}
% }

% \begin{frame}{Haskell}
% \begin{example}
% \begin{minipage}{0.47\textwidth}
% \begin{code}
% data Maybe a
%   = Nothing
%   | Just a
% \end{code}
% \end{minipage}
% \begin{minipage}{0.47\textwidth}
% \begin{code}
% head :: [a] -> Maybe a
% head [] = Nothing
% head (x : xs) = Just x
% \end{code}
% \end{minipage}
% \end{example}
% \end{frame}


% \begin{frame}{Linear Core}
% \item<1-> Core's type-system guarantees 
% \item<2-> A linear Haskell validates
% \end{frame}

% \begin{frame}{GHC Pipeline}
% \begin{itemize}
%   \item<1-> Parser $\to$ Renamer $\to$ Type-checker $\to$ Desugarer
%   \item<2-> Core-to-Core transformations
%       % (transformational approach)
%       % Focus of our work since they transform Core
%       % And we want to validate Core produced by them is still linear
%   \item<3-> Core $\to$ STG $\to$ Cmm $\to$ Backends (x64, ARM, WASM, $\dots$)
% \end{itemize}
% \end{frame}

% \begin{frame}{Optimizing Transformations}
% % \begin{definition}[Term $\beta$-reduction]<1->
% % \[
% % (\lambda x{:}\tau.~e)~y~\Longrightarrow~e[y/x]
% % \]
% % \end{definition}
% \begin{example}[Inlining]<1->
% \[
% \llet{x = 5}{x + x}~\Longrightarrow~\llet{x = 5}{5 + 5}
% \]
% \end{example}
% \end{frame}

% \section{Proposed Work}

\begin{frame}{Typing linearity in Core isn't trivial}
\begin{itemize}
\item Core-to-Core transformations produce programs that aren't accepted by
Core's linear type system
\item The optimizing transformations preserve linearity
\item Core's type-checker needs more information to understand linearity in Core
\end{itemize}
\end{frame}

\begin{frame}{Typing linearity in Core isn't trivial}
\begin{example}[Inlining]<1->
\[
\llet{x = 5}{x + x}~\Longrightarrow~\llet{x = 5}{5 + 5}
\]
\end{example}

\begin{example}[Non-trivial linearity]<2>
\begin{code}
let x = (y, z) in

case e of
  Pat1 -> … x …
  Pat2 -> … y … z …
\end{code}
\end{example}
% \only<2>{
% \begin{example}[$\beta$-reduction violating linearity] % because of laziness
%     \begin{code}
%     f :: a %1 -> a
%     f x = let y = x+2 in y
%     \end{code}
% \end{example}
% }
% \only<3>{
% \begin{example}[Linearity in the presence of laziness] % because of laziness
%     \begin{code}
%     f :: a %1 -> a
%     f x = let y = x+2 in y+y
%     \end{code}
% \end{example}
% }
\end{frame}

\begin{frame}{Proposed Solution}
\begin{itemize}
\item Extend Core's binders with \emph{usage environments}
% Preciso usar e construir
% Entails using the usage environments and 
% \item Augment type system with usage environments to deem more programs linear
% \item Augment the type-checking algorithm to infer usage environments for said bindings
\end{itemize}

\begin{example}[Usage environments]<2>
\[
\begin{array}{lcl}
\llet{x = (y,z)}{...} & & U_x = {y\to1,z\to1}
\end{array}
\]
\end{example}
\end{frame}

\begin{frame}{Proposed Solution}
\begin{example}[Using usage environments]
\[
\begin{array}{l}
\llet{x_{\{y \to 1, z \to 1\}} = (y,z)}{\\ \ccase{e}{\\ ~~Pat1 \to \dots x^{\{y \to 1, z \to 1\}} \dots\\ ~~Pat2 \to \dots y^{\{y \to 1\}} \dots z^{\{z \to 1\}} \dots} }
\end{array}
\]
\end{example}
\end{frame}

\begin{frame}{Proposed Solution}
\begin{example}[Constructing usage environments]
\[
\begin{array}{l}
\llet{x = (y^{\{y\to1\}},z^{\{z\to1\}})}{\\ \ccase{e}{\\ ~~Pat1 \to \dots x \dots\\ ~~Pat2 \to \dots y \dots z \dots} }
\end{array}
\]
\end{example}
\end{frame}

\begin{frame}{The End}
\end{frame}


% Acho que n
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

\begin{frame}{Let Binders}
\begin{definition}[Preliminary Let Typing Rule]<1->
\[
    \infer*[right=(let)]
    {\Gamma \vdash t : A \leadsto \{U\} \\
     \Gamma ; x :_{U} A \vdash u : C \leadsto \{V\}}
    {\Gamma \vdash \text{let } x :_{U} A = t \text{ in } u : C \leadsto \{V\}}
\]
\end{definition}

\begin{example}<2->
\small
\begin{code}
let x = (y, z) in
case e of
  Pat1 -> … x …
  Pat2 -> … y … z …
\end{code}
\end{example}
\end{frame}

\begin{frame}{Recursive Let Binders}
\only<1>{
\begin{definition}[Preliminary Letrec Typing Rule]
\[
    \infer*[right=(letrec)]
    {\Gamma ; x_1 : A_1 \dots x_n : A_n \vdash t_i : A_i \leadsto \{U_{i_\text{naive}}\} \\
     (U_1 \dots U_n) = \mathit{computeRecUsages}(U_{1_\text{naive}} \dots U_{n_\text{naive}}) \\
     \Gamma ; x_1 :_{U_1} A_1 \dots x_n :_{U_n} A_n \vdash u : C \leadsto \{V\}}
    {\Gamma \vdash \text{let } x_1 :_{U_1} A_1 = t_1 \dots x_n :_{U_n} A_n = t_n \text{ in } u : C \leadsto \{V\}}
\]
\end{definition}
}
\only<2>{
\begin{example}
\begin{code}
letrec f z = case z of
        True -> f False
        False -> y
in f True
\end{code}
\end{example}
}
\end{frame}

\begin{frame}{Case Binders}
\begin{definition}[Preliminary Case Typing Rule]
\[
    \infer*[right=(case)]
    {\Gamma \vdash t : D_{\pi_1 \dots \pi_n} \leadsto \{U\} \\
     \Gamma ; z :_{U_k} D_{\pi_1 \dots \pi_n} \vdash b_k : C \leadsto \{V_k\}
     \and V_k \leq V}
    {\Gamma \vdash \ccase{t}{z :_{(U_1\dots U_n)} D_{\pi_1 \dots \pi_n} \{b_k\}_1^m : C \leadsto \{U + V\}}}
\]
\end{definition}
\end{frame}



\end{document}

