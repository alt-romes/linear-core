{-
Bom dia professor, há uma ideia que ainda não consegui formular de coisas
"construtivas" ou "positivas" vs coisas "negativas"

A ideia é que quando forçamos uma coisa positiva no Case, os recursos ainda
estão disponíveis no interior do case, porque forçar uma computação "positiva"
(e.g. vars, construtores) não consome recursos lineares nem os põe no que eu
ando a chamar "ghost resources".  No entanto, forçar uma computação "negativa"
(e.g.  application, cases) vai consumir os recursos lineares do scrutinee e
passá-los para o dito ghost context.

A qualquer momento, um recurso linear `x` ou `y` apenas pode aparecer out no
/linear context/ ou no /ghost linear context/. Desta forma, um `z` com usage
environment `{x,y}` pode ser usado desde que `{x,y}` estejam ou no linear
context, ou no ghost context. Para além disso, recursos lineares no contexto
linear podem ser usados, mas recursos lineares no ghost context não podem ser
usados - têm de ser consumidos através do usage environment de outros recursos.

Os usage environments do case binder e dos patterns seriam iguais
para todos os scrutinees, quer estes fossem positivos ou negativos.

O que difere da regra em que o scrutinee é positivo para a regra em que o
scrutinee é negativo é que forçar um scrutinee negativo "vai por recursos a serem consumidos" (vai passar os recursos do contexto linear para o ghost context).

Pelo contrário, forçar um scrutinee positivo não consome nenhum recurso, por isso os recursos são mantidos.

* Por isso, para positivos, manter os recursos do scrutinee nas alternativas

* Para negativos, mover os recursos do scrutinee para o ghost context

* Em ambos, as linearly bound variables no pattern têm um "fragmented usage
  environment" do scrutinee, e o case binder o "usage environment" do scrutinee

* Em ambos, se não houver linearly bound variables, os recursos do scrutinee são consumidos na totalidade (quer desapareçam do ghost ou do linear environment)
(aqui ainda me chateia o facto de poder haver implementações que requerem que recursos unrestricted sejam forced para consumir os lineares, mas pronto, falha do programador -- o type system deve consegue garantir que isto acontece bem desde que não se use unsafe coerce)


    Γ;Δ;δ ⊦ e ⇑ σ               Γ;Δ,Δ',z{Δ},a{Δ_f1},b{Δ_f2};δ' ⊦ e'
-------------------------------------------------------------------------
          Γ;Δ,Δ';δ,δ' ⊦ case e of z { K a b -> e' } : φ


    Γ;Δ;δ ⊦ e ⇓ σ               Γ;Δ',z{Δ},a{Δ_f1},b{Δ_f2};δ',Δ ⊦ e'
-------------------------------------------------------------------------
          Γ;Δ,Δ';δ,δ' ⊦ case e of z { K a b -> e' } : φ


O problema é que há regras que podem misturar ⇑ e ⇓, tipo a orientação do let depende do body do let...

Exemplos:
-}

-- This is OK since (K1 x y) is positive
f x y = case K1 x y of z
          K1 a b -> (x,y)
          K2 w   -> (x,y)

-- This is NOT OK since (g x y) is negative (eliminates g)
f x y = case g x y of z
          K1 a b -> (x,y)
          K2 w   -> (x,y)

-- E aqui? Só pode ocorrer `x`, o `something y` é negativo, mas o `x` é positivo?
-- Se calhar queremos que ocorrências de variáveis mudem sempre de delta bound para linear? (ver prox exemplo)
f y = let x = something y
       in case x of z
          K1 a b -> _
          K2 w   -> _

f x y =
  let x' = something x
      y' = something y
   in case K x' y' of z
   -- O x e o y podem ocorrer aqui, ou só o x', y'?
        K1 a b -> (x,y)
        K2 w   -> (x,y)
-- Eu diria todos, (o x e o y não são consumidos)
-- Mas no caso da variável isso não funciona porque ao forçar a variável
-- estamos 100% a passar de delta bound para linear bound, porque passamos a
-- ter de consumir o resultado da suspended computation, e os recursos
-- originais deixam de estar disponíveis de todo.
f x y =
  let x' = something x
   in case x' of z
   -- Aqui o x não pode ocorrer de certeza, mas o x' pode.
   -- Como conciliar?
      K1 a b -> (x,y)
      K2 w   -> (x,y)

{-
Conversa com Prof. Toninho:

sadmafioso — Today at 13:02
tu estas a usar a seta para o positivo e o negativo?

romes — Today at 13:11
Sim, exato, mas é um pouco estranho

sadmafioso — Today at 13:12
é um bocado, pq estás a caracterizar expressoes e nao tipos
isso geralmente nao costuma ser flexivel o suficiente
haveria uma forma d usar os tipos para guiar a coisa?
ou é irrelevante?

romes — Today at 13:16
hm, seria interessante

sadmafioso — Today at 13:17
f x y =
  let x' = something x
      y' = something y
   in case K x' y' of z
   -- O x e o y podem ocorrer aqui, ou só o x', y'?
        K1 a b -> (x,y)
        K2 w   -> (x,y)

aqui

romes — Today at 13:17
não tenho a certeza

sadmafioso — Today at 13:18
tu dizes que o x/y pode ocorrer pq o case é de um construtor e portanto o x' e o y' nunca sao forcados
é isso?

romes — Today at 13:18
sim

sadmafioso — Today at 13:18
no fundo o que estas a distinguir sempre no case

romes — Today at 13:18
é que não há nenhuma computação efetivamente

sadmafioso — Today at 13:18
**é entre o caso em que ja esta em WHNF ou nao nao é?**

romes — Today at 13:18
AHA! Sim, exatamente exatamente
Perfeito, é isso mesmo
no caso em que ainda não está em WHNF acontece computação
e já não podemos usar nenhum recurso

sadmafioso — Today at 13:19
e portanto tens de tratar diferente
sim

romes — Today at 13:19
sim.
mas no caso em que está em WHNF não consumimos os recursos.
Mas a variável ainda é especial, porque não podemos assumir que está em whnf ou
não, ou melhor, ao passar de bound variable para whnf passa de delta bound para
linear bound
será possível fazer track de whnformedness ao nível dos tipos?
e há uma conexão bonita entre WHNF e linearity ?

sadmafioso — Today at 13:22
nao
mas teres um caso para o case
(ehhe)
em que ves se esta em WHNF ou nao
ja n é completamente adhoc, parece me

romes — Today at 13:23
pois não! mas como é que o case distingue isso?

sadmafioso — Today at 13:23
a conexao parece-me que estas tu a descobri-la/inventa-la aqui no contexto de lazyness 😛

romes — Today at 13:23
sim, sinto tanbem muito que é isso que está a acontecer

sadmafioso — Today at 13:24
como assim?
é possivel determinar se uma expressao arbitraria esta em WHNF ou nao

romes — Today at 13:24
como é que ao tipificar uma expressão eu sei que ela está ou não em whnf

sadmafioso — Today at 13:24
é uma propriedade decidivel 😛

romes — Today at 13:24
ahh boa, pois, deve ser a história que eu estava a inventar do positivo e negativo
a sério?!

sadmafioso — Today at 13:24
claro q sim

romes — Today at 13:24
isso é um resultado popular?
espetacular

sadmafioso — Today at 13:25
acho eu

romes — Today at 13:25
tem a ver com determinar pode reduzir ou não

sadmafioso — Today at 13:25
deixa me pensar se n estou a dizer asneira

romes — Today at 13:25
se calhar a definição de Valor

sadmafioso — Today at 13:26
intuitivamente parece me decidivel pq e uma propriedade sintactica
relativamente simples
nao estamos a falar de meter uma expressao em WHNF
é testar se

romes — Today at 13:26
excelente
só falta 1 peça, as variáveis
porque o case geral que eu defini em cima para WHNF passa os recursos do scrutinee para o body
mas se tivermos
f x = let y = something x
       in case y of
           K a -> y
 
o x definitivamente /não/ pode ocorrer no corpo do case, mas a regra geral diz que pode, porque os recursos de y são D=x
e y está em WHNF ?
OMG, se calhar é exatamente isso
uma variável é a unica coisa para a qual não sabemos se está em WHNF ou não
por isso temos sempre de avaliar para WHNF antes de fazer pattern match
e é aí mesmo que aplicamos aquela regra para avaliar a váriavel, que passa de Delta para Linear

sadmafioso — Today at 13:33
faz me algum sentido

romes — Today at 13:40
Depois temos de discutir melhor, já começam a cristalizar-se algumas ideias, mas ainda é preciso realmente juntá-las todas num sistema simples e conciso
Mas estou entusiasmado!

sadmafioso — Today at 13:40
teres uma premissa numa regra que "testa" se a expressao do case esta em WHNF ou nao
parece me razoavel
ou algum tweak disso

romes — Today at 13:42
Sim, e conjugamos isso com o /ghost linear context/, com os /fragmented usage
environments/ e com a regra que avalia a variável e muda coisas delta-bound
para linear-bound.

-}

{-
On the /ghost linear context/, /fragmented usage environments/,
evaluating variables to WHNF, and the case rule that branches on whether the
scrutinee is in WHNF:

* Case expressions are difficult to type taking into considerations all the nuances of linearity and evaluation

* They're interesting because its where evaluation vs consumption of linear resources encounter each other

* Forcing an expression to WHNF in the case scrutinee won't really consume all the resources used in the scrutinee
  * Only when the expression is evaluated to NF are all resources used in the expression consumed
    * Rather, when the expression is evaluated to NF or all the linear fields of the WHNF are evaluated to NF
  * Otherwise, evaluation to WHNF will consume /some unknown part/ of the resources
    * We can no longer use the resources in the expression
    * But need to consume the the /remaining unknown part/ of the resources
      * This means using the case binder, which binds to the result of the
        computation that needs to be evaluated in order to consume
      * Or using the linearly-bound variables, which will force the remaining
    * 


Intrinsic connection between evaluating a resource and consuming a resource:
* A resource is only consumed when it is fully evaluated (to NF)

  * Or is it when all linear components are fully evaluated (to NF)?

  * Since if we don't need to necessarily consume the unrestricted resources
    for all the linear resources to have been consumed

* What about unlifted types? (like pattern matching on RealWorld#)?
  * Really, despite (# _, _ #) binding two linear variables, they're already
  fully evaluated, so we don't need to consume them now? Yes, that sounds
  right, but wouldn't that mean we could duplicate RealWorld# inside of the
  case alternative???

* Why must unlifted variables be used exactly once? If we're talking about
  linear unlifted things, it might be that really want to track linearity of
  these unlifted resources, which is uncommon, but might be desired for things
  like RealWorld#?

-}

