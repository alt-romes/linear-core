{-
(Also good to include this in the thesis as an alternative solution and the one we ended up taking)
A simpler alternative to annotating every pattern-bound variable with the constructor and the corresponding pattern position,
we could NOT allow Joining (x:1/2, x:1/2 -> x:1), and to simply split the variables in subsequent constructors further, even if we end up having more of them

  * This means we can no longer type
    
    f x y = case (x,y) of
      (a,b) -> case (x,y) of
        (n,p) -> (a,p)

    Oh, no. Wait. The `x` and `y` in the second case are still whole because we didn't split them up. Meaning we could return (a,n)... which isn't linear semantically.

Still, I was going to say that

  * We get rid of the Join clauses (We only ever split when we need to instantiate variables with fragmented usage environments, we never rebuild the split variables into one)
  * Restricts that special case (actually it doesn't, see above)
  * We don't need complicated positional+constructor arguments
  * We are back to reasonable arithmetic

Turns out it's not quite right.

Nonetheless, I don't think we will ever need the join rule - just don't split things if you don't intend on using them separately.


----------------------------------------

Eu até posso apresentar a prova de soundness sobre a linguagem tal e qual como
ela está, mesmo com a deficência que permite o double free, e depois digo que
remover o que permite o double free seria simples, e apenas implicaria mudar o
outro caso da alternativa, mas que perseguimos outro caminho completamente
diferente muito melhor.


-}
