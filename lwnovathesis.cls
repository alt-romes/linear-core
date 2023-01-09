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


% Use memoir as the base class, for documentation run `texdoc memoir`
% The options set solve (4), (2), (1)
% TODO: For the latex font, use 11pt or 10pt?
\LoadClass[a4paper,11pt,twoside,onecolumn,openright,draft]{memoir}

% TODO: (3) (5) (6) (7)
% \setlrmarginsandblock{2.5cm}{2.5cm}{*}


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


\@ifclassloaded{memoir}{\let\endthesis\relax}{\let\endthesis\endinput
   \ClassError{lwnovathesis}{The lwnovathesis package only works with the memoir class}%
                {\@ehd}}
\endthesis

