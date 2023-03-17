%include polycode.fmt
\renewcommand{\llet}[2]{\mathbf{let}~#1~\mathbf{in}~#2}
\renewcommand{\lletrec}[2]{\mathbf{let~rec}~#1~\mathbf{in}~#2}
\renewcommand{\ccase}[2]{\mathbf{case}~#1~\mathbf{of}~#2}
\newcommand{\judgment}[1]{
    \begin{tabular}{V{2.7}cV{2.7}}
    \hlineB{2.7}
    $#1$\\
    \hlineB{2.7}
    \end{tabular}
}
\newcommand{\datatype}[2]{
  \mathbf{data}~#1~\mathbf{where}~#2
}
\newtheorem{theorem}{Theorem}

\chapter{Linear Core*}

\begin{figure}[h]
\begin{framed}
\[
\begin{array}{l}
%
\textbf{Types} \\
\begin{array}{lcll}
    \varphi,\sigma & ::= & T~\overline{p} & \textrm{Datatype} \\
                   & \mid & \varphi \to_\pi \sigma & \textrm{Function with multiplicity}\\
                   & \mid & \forall p.~\varphi & \textrm{Multiplicity universal scheme}\\
                   % TODO: Eventually Coercions
\end{array}\\\\
%
\textbf{Terms}\\
\begin{array}{lcll}
    u               & ::=  & x,y,z \mid K                           & \textrm{Variables and data constructors}\\
    e               & ::=  & u                                  & \textrm{Term atoms}\\
                    & \mid & \Lambda p.~e~\mid~e~\pi  & \textrm{Multiplicity abstraction/application}\\
                    & \mid & \lambda x{:}_\pi\sigma.~e~\mid~e_1~e_2 & \textrm{Term abstraction/application}\\
                    & \mid & \llet{x{:}_\Delta\sigma = e_1}{e_2}       & \textrm{Let} \\
                    & \mid & \lletrec{\overline{x{:}_\Delta\sigma = e_1}}{e_2}  & \textrm{Recursive Let} \\
                    & \mid & \ccase{e_1}{z{:}_{\overline{\Delta}}~\{\overline{\rho\to e_2}\}}   & \textrm{Case} \\
                    &      &                                    & \\
%    p               & ::= & K~\overline{b{:}\kappa}~\overline{x{:}\sigma} & \textrm{Pattern} \\
    \rho            & ::= & K~\overline{x{:}_\pi\sigma} \mid \_ & \textrm{Pattern and wildcard} \\
% Currently we don't care about the existential multiplicity variables, but later on we might
\end{array}\\\\
%
\textbf{Environments}\\
\begin{array}{lcll}
  \Gamma & ::= & \cdot & \textrm{Empty environment} \\
         & \mid & \Gamma,x{:}_\pi\sigma & \textrm{Lambda bound variable} \\
         & \mid & \Gamma,x{:}_\Delta\sigma & \textrm{Let(rec) bound variable}\\
         % & \mid & \Gamma,x{:}_{\overline{\Delta}}\sigma & \textrm{Case bound variables} -- NOPE
         & \mid & \Gamma,K{:}\sigma & \textrm{Data constructor}\\
         & \mid & \Gamma,p & \textrm{Multiplicity variable}\\
\end{array}\\\\
%
\textbf{Multiplicities}\\
\begin{array}{lcll}
  \pi, \mu & ::= & 1 \mid \omega \mid p \mid \pi + \mu \mid \pi \cdot \mu\\
% We don't use + and cdot yet, but we will
\end{array}\\\\
%
\textbf{Usage Environments}\\
\begin{array}{lcl}
  \Delta & ::= & \cdot \mid \Delta, x{:}_\pi\sigma \mid \Delta+\Delta' \mid \pi\Delta\\
\end{array}\\\\
%
\textbf{Declarations}\\
\begin{array}{lcl}
  pgm & ::= & \overline{decl}; e \\
  decl & ::= & \datatype{T~\overline{p}}{\overline{K:\overline{\sigma \to_\pi}~T~\overline{p}}}
\end{array}
%
\end{array}
\]
\end{framed}
\caption{Linear Core* Syntax}
\label{linear-core-syntax}
\end{figure}



\begin{figure}[h]
\begin{framed}
\small
\[
\begin{array}{c}
    \judgment{\Gamma \vdash e : \sigma}
\\[1em]
    \infer*[right=($Weaken_\omega$)]
    {\Gamma \vdash e : \sigma}
    {\Gamma , x{:}_\omega \sigma \vdash e : \sigma}
\qquad
    \infer*[right=($Weaken_\Delta$)]
    {\Gamma \vdash e : \sigma}
    {\Gamma , x{:}_\Delta \sigma \vdash e : \sigma}
\\[1em]
    \infer*[right=($Contract_\omega$)]
    {\Gamma , x{:}_\omega \sigma, x{:}_\omega \sigma \vdash e : \sigma}
    {\Gamma , x{:}_\omega \sigma \vdash e : \sigma}
\qquad
    \infer*[right=($Contract_\Delta$)]
    {\Gamma , x{:}_\Delta \sigma, x{:}_\Delta \sigma \vdash e : \sigma}
    {\Gamma , x{:}_\Delta \sigma \vdash e : \sigma}
\\[1em]
    \infer*[right=($Var_1$)]
    { }
    {\cdot, x{:}_1 \sigma \vdash x : \sigma}
\qquad
    \infer*[right=($Var_\omega$)]
    { \forall y{:}_\pi\varphi \in \Gamma .~\pi \neq 1 }
    {\Gamma, x{:}_\omega \sigma \vdash x : \sigma}
\qquad
    \infer*[right=($Var_\Delta$)]
    { \Delta\!\upharpoonright_1 = \Gamma }
    {\Gamma , x{:}_\Delta \sigma \vdash x : \sigma}
\\[1em]
    \infer*[right=($\Lambda I$)]
    {\Gamma, p \vdash e : \sigma \and p \notin \Gamma}
    {\Gamma \vdash \Lambda p.~e : \forall p. \sigma}
\qquad
    \infer*[right=($\Lambda E$)]
    {\Gamma \vdash e : \forall p.~\sigma \and \Gamma \vdash_{mult} \pi}
    {\Gamma \vdash e~\pi : \sigma[\pi/p]} % ROMES:TODO: Subsittution the other way around?
\\[1em]
    \infer*[right=($\lambda I$)]
    {\Gamma, x{:}_\pi\sigma_1 \vdash e : \sigma_2}
    {\Gamma \vdash \lambda x{:}_\pi\sigma_1.~e : \sigma_1 \to_\pi \sigma_2}
\qquad
    \infer*[right=($\lambda E$)]
    {\Gamma \vdash e_1 : \sigma_2 \to_\pi \sigma_1 \and \Gamma' \vdash e_2 : \sigma_2}
    {\Gamma,\Gamma' \vdash e_1~e_2 : \sigma_1}
\\[1em]
    \infer*[right=($Let$)]
    {\Gamma, x{:}_\Delta\sigma_1 \vdash e_2 : \sigma_2 \and \Delta \vdash e_1 : \sigma_1 \and \Delta \subset \Gamma}
    {\Gamma \vdash \llet{x{:}_\Delta\sigma_1 = e_1}{e_2} : \sigma_2}
    % em alternativa a isto que está errado (separar o \Gamma em \Gamma, \Delta)
    % \infer*[right=($Let_{Wrong}$)]
    % {\Gamma, x{:}_\Delta\sigma_1 \vdash e : \sigma_2 \and \Delta \vdash u : \sigma_1}
    % {\Gamma,\Delta \vdash \llet{x{:}_\Delta\sigma_1 = u}{e} : \sigma_2}
\\[1em]
    % \infer*[right=($LetRec$)]
    % {\Gamma, \overline{x_n{:}_{\Delta_n}\sigma_n } \vdash e : \varphi \and \overline{\Delta_n \vdash u_n : \sigma_n}}
    % {\Gamma \vdash \lletrec{\overline{x_n{:}_{\Delta_n}\sigma_n = u_n}}{e} : \varphi}
    % ROMES:TODO:FIXME:(later...what???)
    \infer*[right=($LetRec$)]
    {\Gamma, \overline{x{:}_{\Delta}\sigma} \vdash e : \varphi \and \overline{\Delta, \overline{x{:}_{\Delta}\sigma} \vdash e' : \sigma} \and \overline{\Delta \subset \Gamma}}
    {\Gamma \vdash \lletrec{\overline{x{:}_{\Delta}\sigma = e'}}{e} : \varphi}
\\[1em]
    \infer*[right=($Case$)]
    { \Gamma \vdash e_1 : \sigma \and \overline{\Gamma', z{:}_{\Delta_i}\sigma \vdash_{alt} \rho_i \to e_i : \sigma \Rightarrow \varphi} }
    {\Gamma, \Gamma' \vdash \ccase{e_1}{z{:}_{\overline{\Delta}^n}\sigma~\{\overline{\rho_i\to e_i}^n\}} : \varphi}
\\[1em]
    \judgment{\Gamma \vdash_{alt} \rho \to e : \sigma \Rightarrow \varphi}
\\[1em]
    \infer*[right=$(Alt)$]
    { K:\overline{\sigma\to_\pi}~T~\overline{p}\in\Gamma \and \Gamma, \overline{x{:}_\pi\sigma} \vdash e : \varphi}
    {\Gamma \vdash_{alt} K~\overline{x{:}_\pi\sigma} \to e : T~\overline{p} \Rightarrow \varphi}
\qquad
    \infer*[right=$(Alt_\_)$]
    { \Gamma \vdash e : \varphi }
    {\Gamma \vdash_{alt} \_ \to e : T~\overline{p} \Rightarrow \varphi}
\\[1em]
    \judgment{\Gamma \vdash_{mult} \pi}
\\[1em]
    \infer*[right=$(1)$]
    { }
    {\Gamma \vdash 1}
\qquad
    \infer*[right=$(\omega)$]
    { }
    {\Gamma \vdash \omega}
\qquad
    \infer*[right=$(\rho)$]
    { }
    {\Gamma, \rho \vdash \rho}
\\[1em]
\begin{array}{cc}
\judgment{\Gamma \vdash decl : \Gamma'} & \judgment{\Gamma \vdash pgm : \sigma}\\
\\[0.05em]
\infer*[right=$(Data)$]{ }{\Gamma \vdash (\datatype{T~\overline{p}}{\overline{K:\sigma}}) : (\overline{K:\sigma}) } &
\infer*[right=$(Pgm)$]{\overline{\Gamma \vdash decl:\Gamma_d} \and \Gamma = \Gamma_0,\overline{\Gamma_d}\\\\ \Gamma~\mathsf{is~consistent?} \and \Gamma \vdash e : \sigma}{\Gamma_0 \vdash \overline{decl}; e : \sigma}
\end{array}
\end{array}
\]
\end{framed}
\caption{Linear Core* Typing Rules}
\label{linear-core-typing-rules}
\end{figure}


\begin{figure}[h]
\begin{framed}
\small
\[
\begin{array}{l}
%
\textbf{Values} \\
\begin{array}{lcl}
    v & ::= & \Lambda p.~e \mid \lambda x.~e \mid K~\overline{v} \\
\end{array}\\\\
%
\textbf{Evaluation Contexts}\\
\begin{array}{llcl}
\infer{e \longrightarrow e'}{E[e] \longrightarrow E[e']} & E & ::= & \square \mid E~e \mid E~\pi \mid \ccase{E}{z{:}_{\overline{\Delta}}\sigma \{\overline{\rho \to e}\}} \\
\end{array}\\\\
%
\textbf{Expression Reductions}\\
\begin{array}{lcl}
(\Lambda p.~e)~\pi & \longrightarrow & [\pi/p]e\\
(\lambda x.~e)~e' & \longrightarrow & [e'/x]e\\
\ccase{K~\overline{e}}{\dots K~\overline{x{:}_\pi\sigma} \to e'} & \longrightarrow & [\overline{e}/\overline{x{:}_\pi\sigma}]e'\\
% ROMES:TODO: Então e as let bound things? Parece que não conseguimos avançar num let?
\end{array}
\end{array}
\]
\end{framed}
%TODO: Addition and scaling usage environments
\caption{Linear Core* Operational Semantics \small(call-by-name)}
\label{linear-core-operational-semantics}
\end{figure}

\begin{figure}[h]
\begin{framed}
\small
\[
\begin{array}{c}
    \judgment{\Gamma \vdash e : \sigma \leadsto \Delta}
\\[1em]
    \infer*[right=($Var_\pi$)]
    { }
    {\Gamma, x{:}_\pi \sigma \vdash x : \sigma \leadsto \cdot,x{:}_\pi\sigma}
\qquad
    \infer*[right=($Var_\Delta$)]
    { }
    {\Gamma , x{:}_\Delta \sigma \vdash x : \sigma \leadsto \Delta}
\\[1em]
    % \Delta might have p, so on application be careful to substitute
    \infer*[right=($\Lambda I$)]
    {\Gamma, p \vdash e : \sigma \leadsto \Delta \and p \notin \Gamma}
    {\Gamma \vdash \Lambda p.~e : \forall p. \sigma \leadsto \Delta}
\qquad
    \infer*[right=($\Lambda E$)]
    {\Gamma \vdash e : \forall p.~\sigma \leadsto \Delta \and \Gamma \vdash_{mult} \pi}
    {\Gamma \vdash e~\pi : \sigma[\pi/p] \leadsto \Delta[\pi/p]}
\\[1em]
    \infer*[right=($\lambda I_1$)]
    {\Gamma, x{:}_1\sigma_1 \vdash e : \sigma_2 \leadsto \Delta,x{:}_1\sigma_1 \and x{:}_1\sigma_1\notin\Delta}
    {\Gamma \vdash \lambda x{:}_1\sigma_1.~e : \sigma_1 \to_\pi \sigma_2 \leadsto \Delta}
\\[1em]
    \infer*[right=($\lambda I_\omega$)]
    {\Gamma, x{:}_\omega\sigma_1 \vdash e : \sigma_2 \leadsto \Delta}
    {\Gamma \vdash \lambda x{:}_\omega\sigma_1.~e : \sigma_1 \to_\pi \sigma_2 \leadsto \Delta\!\upharpoonright_{\neq x}}
\\[1em]
    \infer*[right=($\lambda E$)]
    {\Gamma \vdash e_1 : \sigma_2 \to_\pi \sigma_1 \leadsto \Delta \and \Gamma \vdash e_2 : \sigma_2 \leadsto \Delta'}
    {\Gamma \vdash e_1~e_2 : \sigma_1 \leadsto \Delta + \Delta'}
\\[1em]
    \infer*[right=($Let$)]
    {\Gamma \vdash e_1 : \sigma_1 \leadsto \Delta \and \Gamma, x{:}_\Delta\sigma_1 \vdash e_2 : \sigma_2 \leadsto \Delta'}
    {\Gamma \vdash \llet{x{:}_\Delta\sigma_1 = e_1}{e_2} : \sigma_2 \leadsto \Delta'}
\\[1em]
    \infer*[right=($LetRec$)]
    { \overline{\Gamma, \overline{x{:}_1\sigma} \vdash e' : \sigma \leadsto \Delta_{naive}}\\
      \overline{\Delta} = \mathsf{computeRecUsages}(\overline{\Delta_{naive}}) \\
      \Gamma, \overline{x{:}_{\Delta}\sigma} \vdash e : \varphi \leadsto \Delta'
      }
    {\Gamma \vdash \lletrec{\overline{x{:}_{\Delta}\sigma = e'}}{e} : \varphi \leadsto \Delta'}
\\[1em]
    \infer*[right=($Case$)]
    { \Gamma \vdash e_1 : \sigma \leadsto \Delta \\
      \overline{\Gamma \vdash_{pat} \rho_i : \sigma \leadsto \Delta_i} \\\\
      \overline{\Gamma', z{:}_{\Delta_i}\sigma \vdash_{alt} \rho_i \to e_i : \sigma \Rightarrow \varphi \leadsto \Delta'} \and
      \overline{\Delta' \leq \Delta''}
      }
    {\Gamma, \Gamma' \vdash \ccase{e_1}{z{:}_{\overline{\Delta}^n}\sigma~\{\overline{\rho_i\to e_i}^n\}} : \varphi \leadsto \Delta + \Delta''}
\\[1em]
    \judgment{\Gamma \vdash_{pat} \rho : \sigma \leadsto \Delta}
\\[1em]
    \infer*[right=($pat$)]
    { }
    {\Gamma, K{:}\overline{\sigma\to_\pi}\varphi \vdash_{pat} K~\overline{x{:}_\pi\sigma}:\varphi \leadsto \cdot,\overline{x{:}_\pi\sigma}}
\\[1em]
    \judgment{\Gamma \vdash_{alt} \rho \to e : \sigma \Rightarrow \varphi \leadsto \Delta}
\\[1em]
    \infer*[right=$(Alt$)]
    { K:\overline{\sigma\to_\pi}~T~\overline{p}\in\Gamma \and \Gamma, \overline{x{:}_\pi\sigma} \vdash e : \varphi \leadsto \Delta}
    {\Gamma \vdash_{alt} K~\overline{x{:}_\pi\sigma} \to e : T~\overline{p} \Rightarrow \varphi \leadsto \Delta}\\
\qquad
    \infer*[right=$(Alt_\_)$]
    { \Gamma \vdash e : \varphi \leadsto \Delta }
    {\Gamma \vdash_{alt} \_ \to e : T~\overline{p} \Rightarrow \varphi \leadsto \Delta}
\end{array}
\]
\end{framed}
\caption{Linear Core* - Infer Usage Environments}
\label{linear-core-construct-usage-envs}
\end{figure}

\section{Type Soundness}

\begin{theorem}[Type preservation]
\emph{If $\vdash e : \sigma$ and $e \to^* e'$ then $\vdash e' : \sigma'$}
\end{theorem}

\begin{proof}
\begin{itemize}
\item Substitution?
\item Context?
\item Structural ?
\item 
\end{itemize}
\end{proof}

\begin{theorem}[Progress]
\emph{Evaluation does not block. If $\vdash e : \sigma$ then $e$ is a value or there exists $e'$ such that $e \to e'$}
\end{theorem}

\begin{proof}
\begin{itemize}
\end{itemize}
\end{proof}

