 (⋆-)
   = \ (@(cat_aoe5 :: Type -> Type -> Type))
       (@r_aoe6)
       (@(con_aoe7 :: Type -> Constraint))
       ($dMonoidal_aoe8 :: Monoidal cat_aoe5)
       ($d(%,%)_aoe9 :: O2 cat_aoe5 r_aoe6 ())
       (df_aoea :: TensorClosed con_aoe7)
       ($d~_aoeb
          :: (con_aoe7 :: (Type -> Constraint))
             ~ (Obj cat_aoe5 :: (Type -> Constraint)))
       (eta_B0 :: S cat_aoe5 r_aoe6)
       (eta_B1 :: S cat_aoe5 r_aoe6) ->
       let {
         $d~_aoHo :: (con_aoe7 :: (Type -> Constraint)) ~ (con_aoe7 :: (Type -> Constraint))
         $d~_aoHo
           = Eq#
               @(Type -> Constraint)
               @con_aoe7
               @con_aoe7
               @~(<con_aoe7>_N
                  :: (con_aoe7 :: (Type -> Constraint))
                     ~# (con_aoe7 :: (Type -> Constraint))) } in
       let {
         $d~_aoHm :: (con_aoe7 :: (Type -> Constraint)) ~ (con_aoe7 :: (Type -> Constraint))
         $d~_aoHm
           = Eq#
               @(Type -> Constraint)
               @con_aoe7
               @con_aoe7
               @~(<con_aoe7>_N
                  :: (con_aoe7 :: (Type -> Constraint))
                     ~# (con_aoe7 :: (Type -> Constraint))) } in
       let {
         irred_aoHi :: Obj cat_aoe5 ()
         irred_aoHi
           = $p1(%,%)
               @(Obj cat_aoe5 r_aoe6) @(Obj cat_aoe5 ()) $d(%,%)_aoe9 } in
       case eq_sel
              @(Type -> Constraint) @con_aoe7 @(Obj cat_aoe5) $d~_aoeb
       of co_aoHb
       { __DEFAULT ->
       case eta_B0 of wild_X1 {

         -- LHS is Compose
         Compose @x_aoee irred_aoef t1_anlR q1_anlS ->

           case eta_B1 of {

            -- and RHS is Compose too
             Compose @x_aoeh irred_aoei t2_anlT q2_anlU ->
               $WCompose
                 @cat_aoe5
                 @(x_aoee ⊗ x_aoeh)
                 @r_aoe6
                 ((df_aoea
                     @x_aoee
                     @x_aoeh
                     (irred_aoef
                      `cast` (Sub (Sym co_aoHb) <x_aoee>_N
                              :: (Obj cat_aoe5 x_aoee :: Constraint)
                                 ~R# (con_aoe7 x_aoee :: Constraint)))
                     (irred_aoei
                      `cast` (Sub (Sym co_aoHb) <x_aoeh>_N
                              :: (Obj cat_aoe5 x_aoeh :: Constraint)
                                 ~R# (con_aoe7 x_aoeh :: Constraint))))
                  `cast` (Sub co_aoHb <(x_aoee, x_aoeh)>_N
                          :: (con_aoe7 (x_aoee, x_aoeh) :: Constraint)
                             ~R# (Obj cat_aoe5 (x_aoee, x_aoeh) :: Constraint)))
                 (∘ @cat_aoe5
                    ($p2Monoidal @cat_aoe5 $dMonoidal_aoe8)
                    @(x_aoee ⊗ x_aoeh)
                    @(Unit ⊗ ())
                    @Unit
                    ((df_aoea
                        @x_aoee
                        @x_aoeh
                        (irred_aoef
                         `cast` (Sub (Sym co_aoHb) <x_aoee>_N
                                 :: (Obj cat_aoe5 x_aoee :: Constraint)
                                    ~R# (con_aoe7 x_aoee :: Constraint)))
                        (irred_aoei
                         `cast` (Sub (Sym co_aoHb) <x_aoeh>_N
                                 :: (Obj cat_aoe5 x_aoeh :: Constraint)
                                    ~R# (con_aoe7 x_aoeh :: Constraint))))
                     `cast` (Sub co_aoHb <(x_aoee, x_aoeh)>_N
                             :: (con_aoe7 (x_aoee, x_aoeh) :: Constraint)
                                ~R# (Obj cat_aoe5 (x_aoee, x_aoeh) :: Constraint)))
                    ((df_aoea
                        @()
                        @()
                        (irred_aoHi
                         `cast` (Sub (Sym co_aoHb) <()>_N
                                 :: (Obj cat_aoe5 () :: Constraint)
                                    ~R# (con_aoe7 () :: Constraint)))
                        (irred_aoHi
                         `cast` (Sub (Sym co_aoHb) <()>_N
                                 :: (Obj cat_aoe5 () :: Constraint)
                                    ~R# (con_aoe7 () :: Constraint))))
                     `cast` (Sub co_aoHb <((), ())>_N
                             :: (con_aoe7 ((), ()) :: Constraint)
                                ~R# (Obj cat_aoe5 ((), ()) :: Constraint)))
                    irred_aoHi
                    (unitor' @cat_aoe5 $dMonoidal_aoe8 @Unit irred_aoHi)
                    (× @cat_aoe5
                       $dMonoidal_aoe8
                       @x_aoee
                       @Unit
                       @x_aoeh
                       @()
                       irred_aoef
                       irred_aoHi
                       irred_aoei
                       irred_aoHi
                       t1_anlR
                       t2_anlT))
                 ((\ (@c_aoeJ) ->
                     let {
                       h_spaQ :: Trie cat_aoe5 (Obj cat_aoe5) r_aoe6 x_aoee
                       h_spaQ
                         = q1_anlS
                             @x_aoee
                             (($WZ @cat_aoe5 @con_aoe7 @x_aoee)
                              `cast` ((Trie <cat_aoe5>_R (Sub co_aoHb) <x_aoee>_N <x_aoee>_N)_R
                                      :: (Trie cat_aoe5 con_aoe7 x_aoee x_aoee :: Type)
                                         ~R# (Trie
                                                cat_aoe5
                                                (Obj cat_aoe5)
                                                x_aoee
                                                x_aoee :: Type))) } in
                     let {
                       h1_spaR :: Trie cat_aoe5 (Obj cat_aoe5) r_aoe6 x_aoeh
                       h1_spaR
                         = q2_anlU
                             @x_aoeh
                             (($WZ @cat_aoe5 @con_aoe7 @x_aoeh)
                              `cast` ((Trie <cat_aoe5>_R (Sub co_aoHb) <x_aoeh>_N <x_aoeh>_N)_R
                                      :: (Trie cat_aoe5 con_aoe7 x_aoeh x_aoeh :: Type)
                                         ~R# (Trie
                                                cat_aoe5
                                                (Obj cat_aoe5)
                                                x_aoeh
                                                x_aoeh :: Type))) } in
                     let {
                       h2_ilxr :: Trie cat_aoe5 con_aoe7 r_aoe6 (x_aoee, x_aoeh)
                       h2_ilxr
                         = :▴:
                             @cat_aoe5
                             @con_aoe7
                             @r_aoe6
                             @(x_aoee, x_aoeh)
                             @x_aoee
                             @x_aoeh
                             @~(<(x_aoee, x_aoeh)>_N
                                :: ((x_aoee, x_aoeh) :: Type) ~# ((x_aoee, x_aoeh) :: Type))
                             (irred_aoef
                              `cast` (Sub (Sym co_aoHb) <x_aoee>_N
                                      :: (Obj cat_aoe5 x_aoee :: Constraint)
                                         ~R# (con_aoe7 x_aoee :: Constraint)))
                             (irred_aoei
                              `cast` (Sub (Sym co_aoHb) <x_aoeh>_N
                                      :: (Obj cat_aoe5 x_aoeh :: Constraint)
                                         ~R# (con_aoe7 x_aoeh :: Constraint)))
                             (h_spaQ
                              `cast` ((Trie
                                         <cat_aoe5>_R (Sub (Sym co_aoHb)) <r_aoe6>_N <x_aoee>_N)_R
                                      :: (Trie cat_aoe5 (Obj cat_aoe5) r_aoe6 x_aoee :: Type)
                                         ~R# (Trie cat_aoe5 con_aoe7 r_aoe6 x_aoee :: Type)))
                             (h1_spaR
                              `cast` ((Trie
                                         <cat_aoe5>_R (Sub (Sym co_aoHb)) <r_aoe6>_N <x_aoeh>_N)_R
                                      :: (Trie cat_aoe5 (Obj cat_aoe5) r_aoe6 x_aoeh :: Type)
                                         ~R# (Trie cat_aoe5 con_aoe7 r_aoe6 x_aoeh :: Type))) } in
                     let {
                       irred3_ilxs :: con_aoe7 (x_aoee, x_aoeh)
                       irred3_ilxs
                         = df_aoea
                             @x_aoee
                             @x_aoeh
                             (irred_aoef
                              `cast` (Sub (Sym co_aoHb) <x_aoee>_N
                                      :: (Obj cat_aoe5 x_aoee :: Constraint)
                                         ~R# (con_aoe7 x_aoee :: Constraint)))
                             (irred_aoei
                              `cast` (Sub (Sym co_aoHb) <x_aoeh>_N
                                      :: (Obj cat_aoe5 x_aoeh :: Constraint)
                                         ~R# (con_aoe7 x_aoeh :: Constraint))) } in
                     \ (ds2_ilxt :: Trie cat_aoe5 con_aoe7 (x_aoee ⊗ x_aoeh) c_aoeJ) ->
                       case ds2_ilxt of wild_ilxu {
                         __DEFAULT ->
                           :∘
                             @cat_aoe5
                             @con_aoe7
                             @r_aoe6
                             @c_aoeJ
                             @(x_aoee, x_aoeh)
                             irred3_ilxs
                             h2_ilxr
                             wild_ilxu;
                         Z co_ilxv ->
                           h2_ilxr
                           `cast` ((Trie <cat_aoe5>_R <con_aoe7>_R <r_aoe6>_N (Sym co_ilxv))_R
                                   :: (Trie cat_aoe5 con_aoe7 r_aoe6 (x_aoee ⊗ x_aoeh) :: Type)
                                      ~R# (Trie cat_aoe5 con_aoe7 r_aoe6 c_aoeJ :: Type))
                       })
                  `cast` (forall (c :: <Type>_N).
                          (Trie <cat_aoe5>_R (Sub co_aoHb) <(x_aoee, x_aoeh)>_N <c>_N)_R
                          %<'Many>_N ->_R (Trie
                                             <cat_aoe5>_R (Sub co_aoHb) <r_aoe6>_N <c>_N)_R
                          :: (forall {c}.
                              Trie cat_aoe5 con_aoe7 (x_aoee, x_aoeh) c
                              -> Trie cat_aoe5 con_aoe7 r_aoe6 c :: Type)
                             ~R# (forall {c}.
                                  Trie cat_aoe5 (Obj cat_aoe5) (x_aoee, x_aoeh) c
                                  -> Trie cat_aoe5 (Obj cat_aoe5) r_aoe6 c :: Type)));

            -- RHS is Plus
             Plus ipv_spa7 ->
               Plus
                 @cat_aoe5
                 @r_aoe6
                 (\ (c_anm0 :: Bool) ->
                    ⋆-
                      @cat_aoe5
                      @r_aoe6
                      @con_aoe7
                      $dMonoidal_aoe8
                      $d(%,%)_aoe9
                      df_aoea
                      ($d~_aoHo
                       `cast` (((~) <Type -> Constraint>_N <con_aoe7>_N co_aoHb)_R
                               :: ((con_aoe7 :: (Type -> Constraint))
                                   ~ (con_aoe7 :: (Type -> Constraint)) :: Constraint)
                                  ~R# ((con_aoe7 :: (Type -> Constraint))
                                       ~ (Obj cat_aoe5 :: (Type -> Constraint)) :: Constraint)))
                      wild_X1 -- the issue was not making the binder unrestricted in these situations
                      (ipv_spa7 c_anm0))
           };

         -- LHS is Plus
         Plus f_anlV ->
           Plus
             @cat_aoe5
             @r_aoe6
             (\ (c_anlX :: Bool) ->
                ⋆-
                  @cat_aoe5
                  @r_aoe6
                  @con_aoe7
                  $dMonoidal_aoe8
                  $d(%,%)_aoe9
                  df_aoea
                  ($d~_aoHm
                   `cast` (((~) <Type -> Constraint>_N <con_aoe7>_N co_aoHb)_R
                           :: ((con_aoe7 :: (Type -> Constraint))
                               ~ (con_aoe7 :: (Type -> Constraint)) :: Constraint)
                              ~R# ((con_aoe7 :: (Type -> Constraint))
                                   ~ (Obj cat_aoe5 :: (Type -> Constraint)) :: Constraint)))
                  (f_anlV c_anlX)
                  eta_B1)
       }
       };,

