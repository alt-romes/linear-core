
{-

G;D;d;[D] |- ...

G ::= . | p,G | x:w,G | K, G
d ::= x:D,[D],D

K => K:w
x => x:w
x:w => x:.,[.]
x:.,[.] <=> x:w


G; D; d; [D]

--------------

* Regra que permite empurrar coisas de `d` para `G`
ou
* Ter um contract explícito para coisas com delta env vazio no d


G ; D ; d ; [D]
U ; L ; A ; L

------(var)
x |- x

não!
------(var)
[x] |- x


---------(varD)
x,[y],z:{x,y} |- z

---------(varD)
x,z:{x,[]} |- z



-}

f x y = let w = use x y (Δ={x,y})
         in case h x y of
              K a b -> Δ={},[Δ]={x,y}
                return w{x,y}

f x y = let w = use x y (Δ={x,y})
         in case h x of
              K a b -> {[x],y}
                return w

f x y = let w = use x (Δ={x})
         in case K x of
              K2 a b -> return w

f x y = let w = use x (Δ={x})
         in case h x of
              K2 a b -> return w -- bad!

f x y =
  case x of
    _ ->
      let w = use x y (Δ={x,y})
      ---ou--
      case h y of
        _ -> return w
      ----- mas isto está bem
      return w
      ----
      case h w of
        _ -> (Δ={[x,y]})

-- este exemplo mostra porque é que é preciso ter os 2 contextos nas delta
-- annotations, pq temos de saber as coisas que já usamos na mesma
f x y =
  case h x of
    K a{x/2-1K} b{x/2-2K} ->
      let w = use a b y (Δ={[x/2,x/2],y})
      return w


-- Como usar os positional binders por constructor

K : \ov{σ ->} φ

Γ;Δ;δ,a{Δ1 -> 1K},b{Δ1 -> 2K},c{Δ1 -> 3K};[Δ] ⊦ e : φ
----------------------------------------------------
Γ;Δ;δ;[Δ] ⊦ K a b c -> e : σ => φ

f x y = case (x,y) of
          (a{xy/2},b{xy/2}) -> case (x,y) of
                     (n{xy/2},p{xy/2}) -> (a{xy/2},n{xy/2})

-- só fractions não é possível, ^^

x:1 |- ...
----------------(split)
x/2,x/2 |- ...

x:1 |- ...
----------------(split)
x/2,x/2 |-_K ...

f x y = case (x,y) of
          (a{xy/1K},b{xy/2K}) -> case (x,y) of
                     (n{xy/1K},p{xy/2K}) -> (a{xy/1K},n{xy/1K}) -- falta usar xy/2K, e usei xy/1K 2x


f x y = case K1 x y of
          K1 a{xy/1K1} b{xy/2K1} -> case K1 x y of
            K2 c{xy/1K2} -> -- {x,y} --> how do I split this? ou faço split para 1K1, 2K1, ou para 1K2
              return (a,b,c)

x:1 |- ...
----------------(split)
x/1K,x/2K |-_K ...


x:1 |- ...
----------------(split)
x/1K2 |-_K2 ...

-- Precisamos de uma regra de split por constructor?
-- (ou uma geral o suficinete q fala sobre todos os constrtores)
-- para um dado construtor, divide sobre todos

f x y = case K1 x y of
          K1 a{xy/1K1} b{xy/2K1} -> case K1 x y of
            K1 c{xy/1K1} d{xy/2K1} -> (a{xy/1K1},d{xy/2K1})
              -- split x into x1K1 e x2K1
              -- can consume those two using a,d or b,c


-- Pensar em tag, em vez de uma fração - simplifica!
--
-- x:1 ... |- e : Φ         K tem 3 linear args
-- ------------------------------------(split)
-- x:1#K_1, x:1#K_2, x:1#K_3 |- e : Φ
--

-- Isto parece ser safe porque só vamos poder usar x#K através de variáveis do
-- padrão que desconstroi uma expressão que usa x

-- * Será possível definir K_1 como multiplicidade?
-- OK, a multiplicidade continua a ser 1

-- Tmb vamos precisar de
--
-- [x:1] ... |- e : Φ         K tem 3 linear args
-- ------------------------------------(split)
-- [x:1#K_1, x:1#K_2, x:1#K_3] |- e : Φ
--
-- porque:

f x y = case h x y of
          K a{[xy]#K_1} b{[xy]#K_2} -> (a,b)

-- A regra do case
--
--
-- K tem n argumentos
-- Γ;Δ;δ,y_1{Δ_s#K_1},...,y_n{Δ_s#K_n};[Δ'] ⊦ e
-- --------------------------------------- (Alt)
-- Γ;Δ;δ;[Δ'] ⊦ K y_1 ... y_n -> e :_Δ_s σ => φ
--
-- No fim temos que o split permite dividir variaveis lineares em coisas com
-- tags que podem ser usadas apenas pelas δ variables introduzidas pelo Case,
-- que tmb vai anotar as divisões do scrutinee
--
-- O objetivo é fazer track de quais bocados do pattern foram usados, porque
-- todos os "bocados" distintos têm de ser usados.

-- engraçado, no início achamos que isto não ia dar
f x y = case (x,y) of
          (a,b) -> case (x,y) of
             (n,p) -> (a,p)
-- só funciona pq fragment resource envs


-- no final acabamos por ter uma regra parecida ao let-bang, que move uma
-- resource do linear para o unrestricted context -- mas o nosso move do affine
-- para o unrestricted (talvez já haja algo assim)
