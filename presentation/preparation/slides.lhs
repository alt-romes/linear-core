\documentclass[14pt,aspectratio=169,dvipsnames]{beamer}
\usetheme{Copenhagen}
%\usetheme{Singapore}
\usecolortheme{spruce}
\usecolortheme{seahorse}
\setbeamertemplate{navigation symbols}{}
\setbeamertemplate{itemize items}[default]
% \setbeamercovered{transparent}
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
    \item<2-> Linear types can \emph<2>{enforce} resource usage invariants
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
\begin{code}
let p = malloc(4);
in free(p);
   free(p);
\end{code}
\end{frame}

\begin{frame}{Haskell}

\end{frame}

\begin{frame}{Linear Haskell}

\end{frame}

\begin{frame}{Core}

\end{frame}

\begin{frame}{System FC}

\end{frame}

\begin{frame}{GHC Optimizations}

\end{frame}

\section{Proposed Work}


\end{document}

