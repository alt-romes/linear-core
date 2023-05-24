-- P :: a ⊸ b ⊸ c ⊸ P a b c
case x of z:p
  P a b c -> ___ z:(a,b,c) && a:1 b:1 c:1
  P _ b _ -> ___ z:p && b:1 -- Invalid... does it happen in Core w/ optimisations?...
  _       -> ___ z:p

P2 :: a -> b ⊸ c -> P a b c
case x of z:p
  P2 a b c -> ___ z:(b) && a:Many b:1 c:Many
  P2 _ b _ -> ___ z:(b) && b:1 -- Invalid... does it happen in Core w/ optimisations?...
  _        -> ___ z:p


-- Our bet
P3 :: a ⊸ b ⊸ c ⊸ P3 a b c
case <expr> of z:{...}
  P3 a b c -> ___ z:(a,b,c) && a:1 b:1 c:1
  P3 _ b _ -> ___ -- won't happen in practice



---------------
., x:1 |- x : σ

\x:1 ->
  case x of z
    _  -> ___ z:should be 1



