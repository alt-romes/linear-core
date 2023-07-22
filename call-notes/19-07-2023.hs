{-
Let's have three case rules:
* Scrutinee is in WHNF
* Scrutinee is not in WHNF and is not a var (are vars in WHNF? kind-of)
* Scrutinee is a var

And the alternative rules are the same for all of them, we simply split the
resources amongst the linearly bound variables, or consume the environment
fully if there are no more linear variables bound in the pattern (i.e. we've reached NF up to linearity, i.e. all linear resources are in NF)
 -}

{-
Provavelmente seria bom olhar para a Permission com fractions da separation logic
Mas a minha ideia agora é que se pode dividir os recursos:

   G, x:1 |- e : T
-------------------------(Split)
G, x:1/2, x:1/2 |- e : T

e pronto, é só isso quase.
com uma regra para tirar recursos do ghost context,

--------------------(Var Delta)
x:D:T ; {D} |- x : T

e outra para tirar do sitio normal

--------------------(Var Delta)
D, x:D:T ; . |- x : T

para usar o a, b dos patterns, é preciso dividir os recursos em fragmentos dos recursos
e como não temos o contract, não dá para usar a várias vezes, por isso as frações são suficientes
(não sei é quanto àquela optimização em que aproveitávamos  a contract como regra admissível)

Ao mantermos dois contextos separados podemos falar das substituições por vazio
(.) sobre as duas ao mesmo tempo, porque têm o mesmo nome, estão é em sítios
diferentes.

Depois também é preciso que na regra da linear variable a linear variable não
possa ser tirada do ghost context
-}
