\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{lwnovathesis}[2023/01/09 NOVA Thesis lightweight class]

% Note [NOVA Thesis]
% ~~~~~~~~~~~~~~~~~~
%
% Requerimentos:
%
% (1) Cada capítulo da dissertação deverá ter início numa página ímpar
% (2) Tipo de letra Arial ou TNR ou semelhante??? Tamanho 10 Arial ou 11 TNR ou ??
% (3) Tamanho 9 e 10 ?? para footnotes e legendas de figuras e tabelas
% (4) Papel A4 210x297 de boa qualidade (80gr)
% (5) Todas as margens de pelo menos 2.5cm
% (6) Line spacing 1 or 1.5 main text
% (7) Line spacing 1 for foot notes, legendas, bibliografia e agradecimentos
% (8) Páginas anteriores ao texto principal (resumos agradecimentos indices etc)
% são numeradas com números romanos em baixo centrado ou à direita, a partir da
% página de rosto
% (9) Todas as páginas do texto são numeradas numa sequência numeração árabe nº
% 1 para cima, em baixo centrado ou à direita. Inclui tudo, mesmo páginas com
% tabelas figuras e anexos
% (10) Subtítulo do capútlo pode estar em cabeçalho ou rodapé (facultativo)??
%
% TODO: Coisas de tabelas e gráficos
%
% Reference: https://www.fct.unl.pt/sites/default/files/desp_n2-cc-2011_normas_para_elaboracao_de_dissertacoes.pdf
%

% Color options for lhs
\PassOptionsToPackage{dvipsnames}{xcolor}

% Use memoir as the base class, for documentation run `texdoc memoir`
% The options set solve (4), (2), (1)
% \LoadClass[a4paper,11pt,twoside,onecolumn,openright,draft]{memoir}
\LoadClass[a4paper,11pt,twoside,onecolumn,openright,draft]{memoir}

% This solves (6) by setting 1.5 line spacing for the main text
% And solves (7) as well because footnotes' line spacing is unaltered
% TODO: (7) for bibliography and acknoledgments must be set manually?
% 
% Nevermind, we use 1 line spacing instead of 1.5
% \OnehalfSpacing

% TODO: (3)

% TODO: Check back on Title section to make cover

% (5)
% Novathesis way
\setlrmarginsandblock{3.0cm}{3.0cm}{*}
\setulmarginsandblock{3.5cm}{2.5cm}{*}
% LW Novathesis way:
% \setlrmarginsandblock{2.5cm}{2.5cm}{*}
% \setulmarginsandblock{2.5cm}{2.5cm}{*}
\checkandfixthelayout

% Use the commands \frontmatter, \mainmatter and \backmatter to define the
% different parts of your thesis. They solve (8) and (9)
%
% * Frontmatter should be used for the initial acknowledgments, indices, etc
%
% * Mainmatter should be used for the main content chapters and everything else
%       including the tables, figures and appendices. I'm not sure about the bibliography.
%
% * Backmatter should not really be used for the thesis if I'm not mistaken, but
%       you might find it useful...
%
% Make sure the numbers are centered at the bottom
\copypagestyle{thesis}{ruled}
\makeevenfoot{thesis}{}{}{\thepage} % Align right page number on even footer
\makeoddfoot{thesis}{}{}{\thepage}  % Align right page number on odd footer

% Use thesis pagestyle defined above
\pagestyle{thesis}

% Abstract
\renewcommand{\abstracttextfont}{\normalfont}
\setlength{\absleftindent}{0cm}
\setlength{\absrightindent}{0cm}

% Indices that open right on new page
% To hide "Contents" from the PDF viewer contents add an asterisk to the command end
\newcommand{\xtableofcontents}{\pdfbookmark{Contents}{Contents}\tableofcontents*\cleardoublepage}
\newcommand{\xlistoffigures}{\listoffigures\cleardoublepage}
\newcommand{\xlistoftables}{\listoftables}


\@ifclassloaded{memoir}{\let\endthesis\relax}{\let\endthesis\endinput
   \ClassError{lwnovathesis}{The lwnovathesis package only works with the memoir class}%
                {\@ehd}}
\endthesis


%%%% Customize %%%%%

% Chapter style
\chapterstyle{veelo}

% Numbering of subsections
\setsecnumdepth{subsection}

% Show until paragraph in TOC
\setcounter{tocdepth}{3}

% Colored links
\usepackage{hyperref}
\hypersetup{colorlinks=true, linkcolor=black, citecolor=magenta, breaklinks, pdfdisplaydoctitle}
% Display document title as PDF title instead of file name

% Display text in blank pages
% \makeatletter
%     \def\cleardoublepage{\clearpage%
%         \if@twoside
%             \ifodd\c@page\else
%                 \vspace*{\fill}
%                 \hfill
%                 \begin{center}
%                 \emph{This page intentionally left blank.}
%                 \end{center}
%                 \vspace{\fill}
%                 \thispagestyle{empty}
%                 \newpage
%                 \if@twocolumn\hbox{}\newpage\fi
%             \fi
%         \fi
%     }
% \makeatother


