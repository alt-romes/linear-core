{-
On context management...

* Proof irrelevant


Todos os contextos:
* ou são distintos ( Γ,Γ'; Δ,Δ'; δ,δ' ; Ω,Ω' ) (unrestricted, linear, delta-bound, proof-irrelevant linear)
* ou estão todos juntos (muito mais precisos na semântica de coisas como "has no linear variables"...)

explicit better than implicit

"Γ has no linear variables -- ..."

Γ' has no linear variables
Γ',Δ ⊦ e : σ
e is in WHNF
{Γ, Δ, z{Δ} ⊦ p -> e :_Δ σ => φ}
----------------------------------
Γ,Γ',Δ ⊦ case e of z {p -> e} : φ

"o que é a que é a tralha toda"
Prof: é delta-bound, linear e proof irrelevant

---------------- (Var Δ)
Δ, x:Δ ⊦ x : σ


Δ,a:Δ ...---
--------------------------------(K)
Δ, a:Δ, Δ', b:Δ' ⊦ K a b : σ

Δ linear variables used in the context
a e b nao são linear, são Δbound, mas os seus Δ e Δ' associados são...


-}

f x y = case g x y of z -- is NOT WHNF
          K a b -> -- {x:1}, {y:1}, a{x:1/2,y:1/2}, b{x:1/2,y:1/2}, z{x:1,y:1}
            case h a b of
              K n p -> ...
            -- or
            case h a b of
              K -> ...
            -- or
            -- Δ_s = {x:1/2, y:1/2, x:1/2, y:1/2} ==> {x:1, y:1}
            case K a b of
              K n p -> -- {x}, {y}, z{x,y} n{x:1/2, y:1/2}, p{x:1/2, y:1/2}, porque não também a{x:1/2, y:1/2}, b{x:1/2, y:1/2}?

{-

Ser explicito sobre a divisão de todos os (4 contextos) seria muito mais
uniforme, explícito, e de certa forma não demasiado difícil de modificar as
provas existentes, com os benefícios de conseguir usar as novas ideias!


~~~~~~~~~~~~~~~~~~~~~~~~~~~~
Vamos separar os 4 contextos
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Prof: Primeiro arranjar as regras

* Fazer primeiro provas para os casos novos


-}


{-

* Sequent Core -- muitas semelhanças a CPS
Se calhar é mais fácil representar ideias lá?
Prof: não


* Mapear de volta para a lógica
** Sistemas graded
** Sub exponentials da lógica linear

Divisão não é novo, tmb acontece no grading
* Separation logic

* WHNF é uma coisa fundamental...

Identificar de forma precisa:
* Falar do "ponto de econtro" entre evaluation e linear consumption of resources

* LinearCalculus(X) ... OutsideIn(X)
** X é a semântica de consumir recursos

* As escolhas "diferentes" que estamos a fazer para as regras são todas driven
pela nossa escolha de definição de "consumir"

Num setting linear, sabemos quando vamos usar, e o call-by-need e call-by-name collapsa
* Tem a ver com Optimal Reduction Strategies para o Cálculo Lambda

TODO: Mudar a operational semantic, neste momento não está bem call-by-need na applicação de função

Como representar thunks e assim? Muitas vezes não são explícitos.
(Existem sistemas com thunks)




* Preciso de Γ e Δ
* Preciso de usage environments
* Coisas que não podem ser usadas, mas precisam de ser consumidas através de outros


A regra da variável pode ser meio justificada por isto
> "but we made numerous choices driven by its role as a compiler"

Próximos passos:
* Fazer o novo sistema
* Com os 4 contextos split
* Como é que a substituição interage com estes contextos? Tentar fazer prova de substituição.
* Por agora não preciso de me preocupar com duplicating resources, pq já não estou a passá-las em lado nenhum, só no caso WHNF of...

- Para provar que no sistema não consigo duplicar recursos era uma prova qq com logical relations


No Sequent Core paper há também uma definição de WHNF

...

Lots of related work, can have a gigantic chapter about it
* call by need and linear lambda calculus
* sequent core
* outside in X
* https://www.cs.cmu.edu/~fp//courses/atp/cmuonly/D92.pdf
* ... others mentioned ...



In Sequent Core they also provide a Logical Interpretation



We're doing the Core-plugin busineess very similarly to Sequent Core: They also
introduced a translation to and from Core, and a section about it in the paper.

-}

{-
mas o TLDR
é que em geral podes fazer built-in de weakening
e contracao
"duplicando" o contexto em todo o lado
e na regra da variavel permitindo um contexto arbitrario
como farias no calculo lambda
se queres eliminar o weakening
a regra da variavel tem so a variavel em questao no contexto
se queres eliminar a contracao
tens de 'dividir' o contexto em cada passo

r: Por isso, se eu dividr o contexto é pq não há contração, e se para Var o contexto estiver vazio é pq não há weakening
   E fica implícito
-}

-- Mais um buraco
f w = case w of
        (a,b) -> a{w/2}, b{w/2}
          case w of
            (c,d) -> c{w/2}, d{w/2}
               (a,c)

{-
A ideia de falar só em números não funciona :)
pq aqui duplicamos o primeiro elemento do par e perdemos o segundo...
é preciso uma forma qualquer de (1) mais genérico: conseguir associar as
frações à posição da variável do pattern, para cada pattern, ou (2) menos
genérico, dizer que todas as variáveis bound no padrão têm de acontecer, e não
se pode usar outras quaiquer (atribuindo um token qualquer a todos os nomes do
pattern)
o (1) naquele exemplo seria tipo
-}

f w = case w of
        (a,b) -> a{w/2-(,)1}, b{w/2-(,)2}
          case w of
            (c,d) -> c{w/2-(,)1}, d{w/2-(,)2}
               (a,c) -- já não seria válido pq estamos a usar duas vezes a posição "1" do (,) ...

-- o (2) seria
f w = case w of
        (a,b) -> a{w/2-tok1}, b{w/2-tok1}
          case w of
            (c,d) -> c{w/2-tok2}, d{w/2-tok2}
               (a,c) -- já não funciona pq estamos a misturar token 1 e token 2

-------------------

-- Ainda mais um buraco
f x y = let w = use x y (Δ={x,y})
         in case h x y of
              K a b -> [Δ]={x,y}
                return w
-- Parece-me que os usage environments têm de saber exatamente a que nível as
-- variáveis ocorreram, não podem só dizer que os usage environments não
-- distinguem entre relevant e proof-irrelevant...

-- Sim, exatamente, todos os usage environments têm de distinguir as variáveis usadas do linear context e do p.i. context.
--
-- O proof irrelevant context é mesmo fundamental para a semântica de laziness x linearidade
-- Porque captura a ideia de os recursos só serem mesmo consumidos no total quando avaliados para normal form (up to linearity)
--
-- Ou seja, permite a existência de recursos que ainda têm de ser consumidos mas que já não podem ser utilizados (e os usage environments preenchem a forma de os consumir)!
--
--
