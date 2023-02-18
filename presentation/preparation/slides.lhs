\documentclass[14pt,aspectratio=169,dvipsnames]{beamer}

\usepackage{todonotes}
\usepackage{cmll}
\usepackage{amssymb}
\usepackage{amsmath}
\usepackage{mathpartir}
\usepackage{fancyvrb}
\usepackage{cleveref}

\newcommand{\parawith}[1]{\paragraph{\emph{#1}}}
\newcommand{\lolli}{\multimap}
\newcommand{\tensor}{\otimes}
\newcommand{\one}{\mathbf{1}}
\newcommand{\bang}{{!}}

\newcommand{\llet}[2]{\mathsf{let}~#1~\mathsf{in}~#2}
\newcommand{\lletrec}[2]{\mathsf{letrec}~#1~\mathsf{in}~#2}
\newcommand{\ccase}[2]{\mathsf{case}~#1~\mathsf{of}~#2}

\usetheme{Copenhagen}
%\usetheme{Singapore}
\usecolortheme{spruce}
\usecolortheme{seahorse}
\setbeamertemplate{navigation symbols}{}
\setbeamertemplate{itemize items}[circle]
\setbeamercovered{transparent}
% \setbeameroption{show notes on second screen}
% \setbeameroption{show notes}

%%%%%%%%%%%%%%  Color-related things   %%%%%%%%%%%%%%
%include polycode.fmt

%subst keyword a = "\textcolor{BlueViolet}{\textbf{" a "}}"

\newcommand{\myFor}[2]{\For{$#1$}{$#2$}}
\newcommand{\id}[1]{\textsf{\textsl{#1}}}

\renewcommand{\Varid}[1]{\textcolor{Sepia}{\id{#1}}}
\renewcommand{\Conid}[1]{\textcolor{OliveGreen}{\id{#1}}}
%%%%%%%%%%%%  End of Color-related things   %%%%%%%%%%%%

\usepackage[utf8]{inputenc}

\title{Type-checking Linearity in Haskell's\\ Core Intermediate Language}
\author{Rodrigo Mesquita and Bernardo Toninho}
\institute{NOVA School of Science and Technology}
\date{\small February 2023}

\begin{document}
\begin{frame}
    \titlepage
    \begin{figure}[htpb]
        \begin{center}
            \vspace*{-1.5cm}
            \includegraphics[width=0.4\linewidth]{../logo_nova.png}
        \end{center}
    \end{figure}
\end{frame}

\section{Introduction}

\begin{frame}{Context}

\begin{itemize}
    \item<1-> Statically typed programs eliminate errors at compile time
    \item<2-> Linear types can enforce resource usage invariants
        % Are expressive types
    % \item<3-> Haskell is a lazy, purely functional programming language
    \item<3-> Linear types were \emph<3>{only recently} introduced in Haskell
    % \item<3-> Linear types were introduced in Haskell, 31 \emph<3>{years} after Haskell's inception.
                % recently introduced
                % Which came with new challenges such as backwards compatibility, future
                % proofing and code re-use
\end{itemize}

\end{frame}

\begin{frame}{Motivation}
\begin{itemize}
    \item<1-> However, linear types were also introduced in \textbf<1>{Core}
        % a typed language that serves as Haskell's main intermediate representation
        % Core is explicitly typed
        % Core is very important because it serves as an internal consistency
        % tool and validation layer of the implementation
    \item<2-> Core programs undergo a myriad of optimizing transformations
        \note{These (core-to-core) transformations follow a modular approach, where
        each transformation produces Core that is further used as input to
        other transformations
        Which might introduce lazy let bindings (through e.g. beta reduction),
        inline definitions, move bindings around (let-floating
        transformations)}
    \item<3-> \textbf<3>{Core's linear type-checker doesn't accept linear
        programs} after optimizing transformations are applied
        % Optimizing transformations destroy linearity as the type-checker sees
        % it. However, we believe optimizing transformations *don't* destroy
        % linearity, it's just a limitation of the type system
    \item<4-> \textbf<4>{Core's linear type-checker is disabled} because
        otherwise disabling optimizations is far worse
        % it doesn't accept transformed Core programs
        % GHC's Core type-checker is disabled because it doesn't accept Core
        % programs that undergo optimizing transformations in Core
        % and otherwise disabling optimizing transformations is not feasible.
\end{itemize}
\end{frame}

\begin{frame}{Objectives}
\begin{itemize}
    \item<1-> Extend Core's type-system to accommodate more linear Core
        % Big distinction between syntatically valid linearity and semantically
        % valid. Transformations result in many semantically valid but
        % syntatically invalid programs, and we need to extend Core to
        % account for this semantic linearity.
    \item<2-> Validate optimizing transformations with the new type-system
    \item<3-> Implement the extensions to Core in GHC
        % , the leading Haskell compiler
\end{itemize}
\end{frame}

\section{Background}

\begin{frame}{Linear Types}
\begin{definition}<1->
% In a linear type system,
Linear resources must be consumed \emph{exactly once}.
\end{definition}
\only<2>{
\begin{example}[Rejected by type-system]
  \begin{code}
  let p = malloc(4);
  in free(p);
     free(p);
  \end{code}
\end{example}
}
\only<3>{
\begin{example}[Accepted by type-system]
  \begin{code}
  let p = malloc(4);
      p' = put(p,5);
  in free(p');
  \end{code}
\end{example}
}
\end{frame}

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

\begin{frame}{Haskell}
\begin{example}
\begin{minipage}{0.47\textwidth}
\begin{code}
data Maybe a
  = Nothing
  | Just a
\end{code}
\end{minipage}
\begin{minipage}{0.47\textwidth}
\begin{code}
head :: [a] -> Maybe a
head [] = Nothing
head (x : xs) = Just x
\end{code}
\end{minipage}
\end{example}
\end{frame}

\begin{frame}{Linear Haskell}

\only<1-5>{
\begin{itemize}
\item<1-> Linear types were retroffited to Haskell by introducing a
    \emph{multiplicity} in the function type
    \begin{itemize}
    \item<2-> A multiplicity of \texttt{1} indicates a linear function ($\to_1$)
    \item<3-> A multiplicity of \texttt{Many} indicates an unrestricted function ($\to_\omega$)
    \item<4-> For example, $\mathsf{id}:: a~\%1 \to a$
    \end{itemize}
    % Which has good benefits such as backwards compatibility and code
    % re-use, which are very important in the context of
\item<5-> A linear function must consume its argument \emph{exactly once}
% \begin{example}
% \begin{code}
% id :: a %1 -> a
% \end{code}
% \end{example}
\end{itemize}
}

\only<6-8>{
\begin{definition}[Consuming a value]
  \begin{itemize}
    \item<6-> To consume a value of atomic base type, just evaluate it
    \item<7-> To consume a function exactly once, apply it, and consume the
    result
    \item<8-> To consume a value of an algebraic data type, pattern-match on
    it, and consume its linear components
  \end{itemize}
\end{definition}
}

\only<9>{
\begin{example}[Linear types in Haskell]
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
\end{example}
}

\only<10>{
\begin{example}[Multiplicity polymorphism]
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
\end{example}
}
\end{frame}

\begin{frame}{Core}

\begin{itemize}
\item<1-> Core is a minimal explicitly typed functional language
\item<2-> The whole of Haskell can be desugared to Core % it's its main intermediate representation
  \begin{itemize}
    \item<3-> Core allows us to reason about the entirety of Haskell in a much smaller language.
    % \item<4-> The entirety of Haskell can be compactly expressed in Core
    \item<4-> Analysis, optimization and code generation is performed on Core
    % transformational approach to optimization
    \item<5-> Type-checking Core serves as internal consistency tool
    % for the desugaring and optimization passes
  \end{itemize}
% \item<6-> Core type-checker is much faster than Haskell
\item<6-> Core is based on the $System~F_C$ type-system
\end{itemize}

\end{frame}

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

% \begin{frame}{Linear Core}
% \item<1-> Core's type-system guarantees 
% \item<2-> A linear Haskell validates
% \end{frame}

\begin{frame}{GHC Optimizations}
\begin{itemize}
  \item<1-> Parser $\to$ Renamer $\to$ Type-checker $\to$ Desugarer
  \item<2-> Core-to-Core transformations (transformational approach)
  \item<3-> Core $\to$ STG $\to$ Cmm $\to$ Backends (x86_64, ARM, WASM,$\dots$)
\end{itemize}
\end{frame}

\section{Proposed Work}


\end{document}

