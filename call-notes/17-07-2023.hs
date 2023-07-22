{-


* Escrever os 3 passos da transformação do Simon
* Escrever o programa do double free que não pode estar well-typed


-- para realmente fechar a handle, resultado tem de ser consumido
close :: Handle -o RW# -o (# String, RW# #)

map :: (a -o b) -> [a] -o [b]

--

Em call-by-need, os recursos passados a uma função só são consumidos quando o resultado da função é consumido. (Linear Haskell agrees)

Definition 2.1 (Consume exactly once).
• To consume a value of atomic base type (like Int or Ptr) exactly once, just evaluate it. (NF)
• To consume a function value exactly once, apply it to one argument, and consume its result
exactly once. (β)
• To consume a pair exactly once, pattern-match on it, and consume each component exactly
once. (WHNF)
• In general, to consume a value of an algebraic datatype exactly once, pattern-match on it,
and consume all its linear components exactly once (Sec. 2.5).

--

[suspended computation]
==force==>
[resource (string)] -- tem de ser consumido linearmente, para fazer sentido termos consumido os suspended resources


    Δ,xΔσ ⊦ x:σ   Γ,x1!σ ⊦ e : τ
    ----------------------------- (unsuspend)
        Γ,Δ,xΔσ ⊦ !x; e : τ


    Δ,xΔσ ⊦ x:σ    Γ, x1!σ, (a,b,c):x, z:x ⊦ e : τ
    -----------------------------------------------(unsuspend)
        Γ,Δ,xΔσ ⊦ case !x of z { (...) -> e } : τ


let x = close handle rw -- thunk -- suspended computation -- suspended resources (handle, rw)

!x -- result of suspended computation



x -> WHNF consumimos algumas resources
x -> NF consumimos todas as resources
vs
x -> WHNF consumimos todas resources



-}


f x = case x of z { K a b -> expensive z }

===>
data K a b = K a b
x :: K a b
g ... = let y = ... in f y

f x = case x of z { K a b -> expensive x }
-- x:1 is
-- * evaluated (case x of -- noop)
-- * not evaluated (case x of -- evaluates, move from Δ -> 1)


{--
 Ao passar WHNF ->
  * os recursos que estavam suspensos já 
  * Só que ainda não foram consumidos.

xΔ |- x       { Δ,zΔ |- e }
---------------------------
  case x of z { K... -> e }


close :: Handle -o K 1 ω
close = ...
there could be a bad implementation of close that only consumed Handle when the unrestricted argument (ω) is forced

-}

f x = case x of z { K a b -> expensive x
                  ; K     -> x -- e isto? não!
                               -- K está em NF, por isso todos os recursos foram consumidos,
                               -- x já foi consumido -- não podemos usar x nem z.
                  }
-- * Quando for executar, dentro da alternativa recurso pointed to by x is in WHNF
-- * Usar o x é OK (pq a,b, e z não ocorrem), estamos a devolver o que foi computado (alguém vai ter de me consumir)
-- * Usar o z (que é só x), funciona da mesma forma.

===>

f x = case x of z { K a b -> expensive z }

--- conciliar case var of ... com case expr of ...


close :: Handle -> IO ()




f x = case x of z { K a b -> expensive x; K2 w -> w }

-- f handle rw = case close handle rw of z { K a b -> expensive x; K2 w -> w }

{-

Num constructor alt:
* 

-}




f x = case x of z { K a b -> expensive x; K2 w -> w }


f y = let x = use y
       in case x of z { K a b -> expensive x; K2 w -> w }


f y = let x = use y
      let t = expensive x
       in case x of z { K a b -> t; K2 w -> w }




-- not well typed
f handle2 rw2 =
  case hClose handle2 rw2 of z
    _ -> case hClose handle2 rw2 of -- well-typed double free?
        (# (), rw4 #) -> return (# Ur (), rw4 #)


--
-- * Binder swap + reverse binder swap
--
--
-- Abandonar estas 2^ e deixar de ter o caso do wildcard especial
--
-- ...
--
--
--
--




g handle2 rw2
  = case hClose handle2 rw2 (Δ=handle2,rw2) of z
      (# x, rw3 #) -> -- Δ não pode ocorrer
                      -- alguma parte já foi usado
                      -- e agora temos de consumir x, rw3 para "finalizar" o consumo do scrut.
                      --
                      -- Δ_1/2, x:{Δ_1/4}, rw3{Δ_1/4}, z{Δ_1/2}

g handle2 rw2
  = let x = hClose handle2 rw2 -- suspended (handle2,rw2), but if we never start evaluating, we never start consuming
     in case hClose handle2 rw2 of z
          (# (), rw3 #) ->


g handle2 rw2
  = let x = hClose handle2 rw2
     in case x (Δ=handle2,rw2) of z
          (# (), rw3 #) -> -- x pode ocorrer se rw3 n aparecer,
                           -- porque agora que avaliamos x,
                           -- temos de consumir o "resultado de x",
                           -- que está guardado em x (thunk is overwritten)

g x
  = case x (Δ=handle2,rw2) of z
     (# (), rw3 #) -> -- x pode ocorrer se rw3 n aparecer,
                      -- porque agora
                      -- * ou fizemos noop pq x já estava avaliado, mas temos de consumir o "resto" de x na mesma (por isso podemos usar x)
                      -- * ou avaliamos x,
                      -- temos de consumir o "resultado de x",
                      -- que está guardado em x (thunk is overwritten)

-- como diferenciar os case scrut?
case x of -- podiamos mapear para a outra regra, como um caso especial

-- então e
case (let y = x in y) (Δ=x) of ...

-- quando avaliamos uma variavel para WHNF
--
-- quando avaliamos uma expressao, não sabemos exatamente quais recursos foram
-- postos em WHNF, por isso nao podemos contar com isso

-- se soubesse que avaliar close poem handle em WHNF mas nao o consome completamente,
-- poderia usar handle no body, mas não sei isso para <expr>, mas sei para <var>!
case close handle rw of

-- mas conseguimos ver <let y = x in y> como <var>?
-- se calhar não precisamos de ser tão smart

-- quando avalio uma variável
-- * ou está em normal form
-- * ou avalio, e tenho de consumir o resultado de avaliar



-- g handle2 rw2 =
--   case hClose handle2 rw2 of z
--     (# (), rw3 #) ->
--         case hClose handle2 rw2 of -- well-typed double free
--             (# (), rw4 #) -> return (# (), rw4 #)


































{-

File stuff

case hClose handle2 rw2 of z
  (# (), rw3 #) ->
      case hClose handle2 rw2 of -- well-typed double free
          (# (), rw4 #) -> return (# (), rw4 #)



f :: RealWorld# -> (# (), RealWorld# #)
f rw0 =
  case openFile "test.txt" ReadMode rw0 of
    (# handle1, rw1 #) ->
      case hPutStrLn handle1 "hello there" rw1 of
        (# handle2, rw2 #) ->
          case hClose handle2 rw2 of
            (# (), rw3 #) ->
              return (# (), rw3 #)






-}
