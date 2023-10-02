<!-- The first attempt of an implementation tried converting from Core to Linear Core -->
<!-- first, and then typecheck linear core separately. -->
<!-- Apart from a bit contrived and likely more complicated (how to remove type -->
<!-- applications, coercions, pattern synonyms, AppTy, etc...), the system changed -->
<!-- considerably towards the end, so we reimplemented it from scratch: -->

<!-- Currently, the only modules that are not outdated with dropped implementations are -->
<!-- `Linear.Core`, `Linear.Core.Monad`, and the first part of `Linear.Core.Plugin`. -->

<!-- Later on we can move them out of the package into an "outdated things" one, but -->
<!-- for now it doesn't matter. -->

<!-- --- -->

Reproducing results

<!-- ``` -->
<!-- ghc -fplugin=... depends on linear-core-prototype -->
```
```
cat output | grep -A1 FAILED | sort | uniq | wc
cat output | grep SUCCESS | awk '{print $2}' | paste -s -d+ | bc
```

### priority-sesh

WIP
```haskell
   $ccancel_s46Z :: forall {a}.  Cancelable a => [a] %1 -> State# RealWorld %1 -> (# State# RealWorld, () #)
   $ccancel_s46Z
     = \ (@a_a2DK) ($dCancelable_a2DL  :: Cancelable a_a2DK) (eta_B0  :: [a_a2DK]) (eta_B1  :: State# RealWorld) ->
         letrec {
           go_s48m :: [a_a2DK] %1 -> State# RealWorld %1 -> (# State# RealWorld, [()] #)
           go_s48m
             = \ (ds_a46v  :: [a_a2DK])
                 (eta_X2  :: State# RealWorld) ->
                 case ds_a46v of {
                   [] -> (# eta_X2, [] @() #);
                   : x_a46y  xs_a46z  ->
                     case $dCancelable_a2DL x_a46y eta_X2 of
                     { (# ipv_a46O, ipv1_a46P #) ->
                         case go_s48m xs_a46z ipv_a46O of {
                         (# ipv2_a46S, ipv3_a46T #) -> (# ipv2_a46S, : @() ipv1_a46P ipv3_a46T #)
                     }
                     }
                 }; } in
         case go_s48m eta_B0 eta_B1 of
         { (# ipv_a45T, ipv1_a45U #) ->
         (# ipv_a45T,
            case $w$cconsume
                   @()
                   ($fConsumable()1 `cast` (N:Generically[0] <()>_R %<'One>_N ->_R N:Generically[0] <()>_R ; Sym (N:Consumable[0] <()>_N) :: (Generically () %1 -> Generically () :: Type) ~R# (Consumable () :: Constraint)))
                   ipv1_a45U
            of
            { (# #) -> () } #)
         },
```


### linear-smc

Success: 19438+ (over 7 modules)
Failed: 4 in total, 1 unique
Reasons for failure: Reverse binder swap argument


### linear-base

Success: 83476+ (over 89 modules)
<!-- Failed: 890 in total, 80 unique -->
Failed: 820 in total, 74 unique
Reasons for failure:
NB: It is amazing how this allows us to see examples of semantically linear
programs (which was kind of impossible with -dlinear-core), modulo all the ones
we can already type. It's great progress...

Is linear because all possible constructors have no linear components:
```haskell
(&&)
 = \ (ds_dWT :: Bool) (ds_dWU :: Bool) ->
     case ds_dWT of {
       False -> case ds_dWU of { __DEFAULT -> False };
       True -> ds_dWU
     },
```

Is linear because `ds_dWT` becomes an unrestricted variable in the `False`
branch, just like `wild_X1`. However, as with the reverse binder swap, this
program is not linear if we consider call-by-name evaluation of this linear
function application to an argument using linear resources.
```haskell
(&&)
 = \ (ds_dWT [Dmd=SL] :: Bool) (ds_dWU [Dmd=SL] :: Bool) ->
     case ds_dWT of wild_X1 [Dmd=A] {
       False -> case ds_dWU of wild_X2 [Dmd=A] { __DEFAULT -> ds_dWT };
       True -> ds_dWU
     },
```

Another case of a function that is linear but whose application cannot be
evaluated call-by-name (as in the reverse binder swap section is explained).
```haskell
   ($!)
     = \ (@(rep_a7KY :: RuntimeRep))
         (@a_a7KZ)
         (@(b_a7L0 :: TYPE rep_a7KY))
         (@(p_a7L1 :: Multiplicity))
         (@(q_a7L2 :: Multiplicity))
         (f_a7E1 :: a_a7KZ %p_a7L1 -> b_a7L0)
         (a_a7E2 :: a_a7KZ) ->
         case a_a7E2 of a_X0 { __DEFAULT -> f_a7E1 a_a7E2 },
```

Funny CSE situation, but we are not able to see this.
```haskell
lvl_s82t
 = \ (@a_a7ZP) (ds_d81A [Dmd=S!P(L)] :: Ur a_a7ZP) ->
     case ds_d81A of wild_X1 [Dmd=A] { Ur x'_a7Vy ->
     (ds_d81A, ds_d81A)
     },
```


I'm not sure how this is linear, `c_d8Hn` takes an unrestricted argument, but is
given a linear one. This may have been caused by a rewrite rule.
```haskell
take :: forall a. Int -> Replicator a %1 -> [a]
take
 = \ (@a_a8DQ) (ds_d8Hk :: Int) (r_a8u5 :: Replicator a_a8DQ) ->
     case ds_d8Hk of { I# ds_d8Hs ->
     case ds_d8Hs of ds_X2 {
       __DEFAULT ->
         case next @a_a8DQ r_a8u5 of { (a_a8u9, r'_a8ua) ->
         : @a_a8DQ a_a8u9 (take @a_a8DQ (I# (-# ds_X2 1#)) r'_a8ua)
         };
       0# -> case consume @a_a8DQ r_a8u5 of { () -> [] @a_a8DQ };
       1# ->
         build
           @a_a8DQ
           (\ (@a_d8Hm)
           -- Isto é linear pq c_d8Hn vai ser sempre (:) Cons
              (c_d8Hn [OS=OneShot] :: a_a8DQ -> a_d8Hm -> a_d8Hm)
              (n_d8Ho [OS=OneShot] :: a_d8Hm) ->
              c_d8Hn (extract @a_a8DQ r_a8u5) n_d8Ho)
     }
     };,
```

Same $CaseVar$ issue with call-by-name evaluation.
```haskell
duplicate
 = \ (@a_a8Db) (ds_d8Ha [Dmd=SL] :: Replicator a_a8Db) ->
     case ds_d8Ha of wild_X1 [Dmd=A] {
       Moved x_a8tq [Dmd=S] -> Moved @(Replicator a_a8Db) ds_d8Ha;
       Streamed stream_a8tr [Dmd=S!P(S,S,S,S)] ->
         Streamed
           @(Replicator a_a8Db)
           (case stream_a8tr of wild_i8Iw [Dmd=A]
            { ReplicationStream @s_i8Ix s1_i8Iy give_i8Iz dups_i8IA
                                consumes_i8IB ->
            ReplicationStream
              @(Replicator a_a8Db)
              @s_i8Ix
              s1_i8Iy
              (\ (x_i8HV :: s_i8Ix) ->
                 Streamed
                   @a_a8Db
                   ($WReplicationStream
                      @s_i8Ix @a_a8Db x_i8HV give_i8Iz dups_i8IA consumes_i8IB))
              dups_i8IA
              consumes_i8IB
            })
```

<!-- EmptyCase: It looks as undefined behaviour in our system, but really it just -->
<!-- works, as checking the scrutinee works, and there are no alternatives to check. -->
<!-- Basically, it simply succeeds as no more evaluation needs to happen. So I -->
<!-- suppose this should work. Ok, fixed. -->
<!-- ``` -->
<!-- $cconsume_abPH = \ (ds_dcfV :: Void) -> case ds_dcfV of { }, -->
<!-- ``` -->

Case DEFAULT when all constructors have no linear fields
```
$cconsume_scgJ
 = \ (ds_X3 :: Generically Bool) ->
     case ds_X3
          `cast` (N:Generically[0] <Bool>_R
                  :: (Generically Bool :: Type) ~R# (Bool :: Type))
     of
     { __DEFAULT ->
     ()
     },
```

As in the next one, I'm not sure if this is semantically linear; `ww_ssAa` is
not being consumed. This only occurs in once iteration of the program... perhaps
there is an invalid temporary state?
```haskell
join
$j_ssvi :: Ur Bool %1 -> Set Int %1 -> Ur (TestT IO ())
$j_ssvi (a_ssA2 :: Ur Bool) (b_ssA6 :: Set Int)
  = case a_ssA2 of wild_00 {
      Ur ww_ssA4 ->
        case b_ssA6  of wild_00 {
          HashMap ww_ssA8 ww_ssA9 ww_ssAa(%1) ->
          jump $w$j_ssAd ww_ssA4
        }
  }
```

Why is this one linear? It really seems as though `ww_ssAa` (a linear resource)
is not consumed, so `ww4_as4w` hence `ww_ssAj` aren't consumed linearly...
Perhaps some optimisation butchered this program's linearity
```haskell
$wlvl_ssAm :: Int# -> Int# -> Array# (Maybe (RobinVal Int ())) %1 -> Ur (TestT IO ())
$wlvl_ssAm
  = \ (ww_ssAh :: Int#)
      (ww_ssAi :: Int#)
      (ww_ssAj :: Array# (Maybe (RobinVal Int ()))) ->
      case ($winsert @Int @() $d(%,%)_arFO y_aba2 () ww_ssAh ww_ssAi ww_ssAj)
           `cast` (Identity (HashMap Int ()) ~R# HashMap Int ())
      of
      { HashMap ww_as4q ww1_as4r ww2_as4s ->
      case $wlookup
             @Int @() $d(%,%)_arFO y_aba2 ww_as4q ww1_as4r ww2_as4s
      of
      { (# ww3_as4v, ww4_as4w #) ->
      case ww3_as4v of { Ur ds1_as4z ->
      case ds1_as4z of {
        Nothing ->
          case ww4_as4w of
          { HashMap ww_ssA8 ww_ssA9 ww_ssAa ->
          lvl_ssGG
          };
        Just ds2_as4D ->
          case ww4_as4w of
          { HashMap ww_ssA8 ww_ssA9 ww_ssAa ->
          lvl_ssGH
          }
      }
      }
      }
      }
```

An error caused by ignoring casts. We have a non-linear function that is
unsafely coerced to a linear function then applied to a linear resource.
Because we don't apply the cast to get the function type to be linear, we don't
accept the program
(ww_szqt, x_axYI, eta1_X2)
```haskell
$wlvl_szqw
 = \ (ww_szqt :: Array# Int) ->
     case unsafeEqualityProof @Multiplicity @'Many @'One of
     { UnsafeRefl co_axYM ->
     case ((\ (ds1_axYL [OS=OneShot] :: Array# Int) ->
              (# Ur
                   @Int
                   (I#
                      (sizeofMutableArray#
                         @'Lifted
                         @RealWorld
                         @Int
                         (ds1_axYL
                          `cast` (N:Array#[0] <Int>_N
                                  :: (Array# Int :: UnliftedType)
                                     ~R# (MutableArray#
                                            @{'Lifted} RealWorld Int :: UnliftedType))))),
                 ds1_axYL #))
           `cast` (<Array# Int>_R
                   %(Sym co_axYM) ->_R <(# Ur Int, Array# Int #)>_R
                   :: (Array# Int -> (# Ur Int, Array# Int #) :: Type)
                      ~R# (Array# Int %1 -> (# Ur Int, Array# Int #) :: Type)))
            ww_szqt
     of
     { (# ipv_axYR [Dmd=1!P(1!P(1L))], ipv1_axYS #) ->
     case ipv_axYR of { Ur size'_axYV [Dmd=1!P(1L)] ->
     case size'_axYV of { I# unbx_axZ2 [Dmd=1L] ->
     case $wpop @Int unbx_axZ2 ipv1_axYS of
     { (# ww2_az7c [Dmd=1!A], ww3_az7d [Dmd=1!P(L,L)] #) ->
     case ww2_az7c of { Ur a1_ay4J [Dmd=A] ->
     case ww3_az7d of { Vec ww_az71 ww1_az72 ->
     $wtoList @Int ww_az71 ww1_az72
     }
     }
     }
     }
     }
     }
     },
```
Same thing for (eta1_X2):
```
elim3 :: forall a. (a %1 -> a %1 -> a %1 -> [a]) %1 -> V 3 a %1 -> [a]
```
1 Oct: The plugin seems to hang when linking, after validating all programs, for some reason I don't understand, but only on linear base...

