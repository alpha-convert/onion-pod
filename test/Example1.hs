{-
t = inlineElims (Let "x" (CatR (IntR 3) (IntR 4)) (CatL "a" "b" "x" (CatR (Var "a" TyInt) (Var "b" TyInt))))
code = Imperative.Stream.sToList $ Imperative.Sem.semElimTerm t (Imperative.Stream.sFromList [])
ppr <$> unTypeCode code
-}

do {inp_ref_0 <- GHC.STRef.newSTRef [];
    intSent_ref_1 <- GHC.STRef.newSTRef GHC.Types.False;
    intSent_ref_2 <- GHC.STRef.newSTRef GHC.Types.False;
    finished_e1_3 <- GHC.STRef.newSTRef GHC.Types.False;
    sref_4 <- GHC.STRef.newSTRef Types.TyInt;
    intSent_ref_5 <- GHC.STRef.newSTRef GHC.Types.False;
    intSent_ref_6 <- GHC.STRef.newSTRef GHC.Types.False;
    finished_e1_7 <- GHC.STRef.newSTRef GHC.Types.False;
    seenCatPunc_8 <- GHC.STRef.newSTRef GHC.Types.False;
    sref_9 <- GHC.STRef.newSTRef Types.TyInt;
    finished_e1_10 <- GHC.STRef.newSTRef GHC.Types.False;
    acc_ref_11 <- GHC.STRef.newSTRef GHC.Types.[];
    let {loop_12 = do {e1_done_13 <- GHC.STRef.readSTRef finished_e1_10;
                       if GHC.Classes.not e1_done_13
                        then do {t_14 <- GHC.STRef.readSTRef sref_4;
                                 if Types.isNull t_14
                                  then GHC.STRef.writeSTRef finished_e1_10 GHC.Types.True GHC.Base.>> (do {acc_15 <- GHC.STRef.readSTRef acc_ref_11;
                                                                                                           GHC.STRef.writeSTRef acc_ref_11 (acc_15 GHC.Base.++ [Events.CatPunc]);
                                                                                                           loop_12})
                                  else do {e1_done_16 <- GHC.STRef.readSTRef finished_e1_3;
                                           if GHC.Classes.not e1_done_16
                                            then do {intSent_17 <- GHC.STRef.readSTRef intSent_ref_1;
                                                     if GHC.Classes.not intSent_17
                                                      then GHC.STRef.writeSTRef intSent_ref_1 GHC.Types.True GHC.Base.>> (case Events.CatEvA (Events.IntEv 3) of
                                                                                                                          {Events.CatEvA ev_18 -> do {let {ev_19 = ev_18};
                                                                                                                                                      Data.STRef.modifySTRef sref_4 (`Events.deriv` ev_19);
                                                                                                                                                      do {acc_20 <- GHC.STRef.readSTRef acc_ref_11;
                                                                                                                                                          GHC.STRef.writeSTRef acc_ref_11 (acc_20 GHC.Base.++ [Events.CatEvA ev_19]);
                                                                                                                                                          loop_12}}})
                                                      else GHC.STRef.writeSTRef finished_e1_3 GHC.Types.True GHC.Base.>> (case Events.CatPunc of
                                                                                                                          {Events.CatEvA ev_21 -> do {let {ev_22 = ev_21};
                                                                                                                                                      Data.STRef.modifySTRef sref_4 (`Events.deriv` ev_22);
                                                                                                                                                      do {acc_23 <- GHC.STRef.readSTRef acc_ref_11;
                                                                                                                                                          GHC.STRef.writeSTRef acc_ref_11 (acc_23 GHC.Base.++ [Events.CatEvA ev_22]);
                                                                                                                                                          loop_12}}})}
                                            else do {intSent_24 <- GHC.STRef.readSTRef intSent_ref_2;
                                                     if GHC.Classes.not intSent_24
                                                      then GHC.STRef.writeSTRef intSent_ref_2 GHC.Types.True GHC.Base.>> (case Events.IntEv 4 of
                                                                                                                          {Events.CatEvA ev_25 -> do {let {ev_26 = ev_25};
                                                                                                                                                      Data.STRef.modifySTRef sref_4 (`Events.deriv` ev_26);
                                                                                                                                                      do {acc_27 <- GHC.STRef.readSTRef acc_ref_11;
                                                                                                                                                          GHC.STRef.writeSTRef acc_ref_11 (acc_27 GHC.Base.++ [Events.CatEvA ev_26]);
                                                                                                                                                          loop_12}}})
                                                      else GHC.STRef.writeSTRef finished_e1_10 GHC.Types.True GHC.Base.>> (do {acc_28 <- GHC.STRef.readSTRef acc_ref_11;
                                                                                                                               GHC.STRef.writeSTRef acc_ref_11 (acc_28 GHC.Base.++ [Events.CatPunc]);
                                                                                                                               loop_12})}}}
                        else do {t_29 <- GHC.STRef.readSTRef sref_9;
                                 if Types.isNull t_29
                                  then GHC.STRef.readSTRef acc_ref_11
                                  else do {b_30 <- GHC.STRef.readSTRef seenCatPunc_8;
                                           if b_30
                                            then do {e1_done_31 <- GHC.STRef.readSTRef finished_e1_7;
                                                     if GHC.Classes.not e1_done_31
                                                      then do {intSent_32 <- GHC.STRef.readSTRef intSent_ref_5;
                                                               if GHC.Classes.not intSent_32
                                                                then GHC.STRef.writeSTRef intSent_ref_5 GHC.Types.True GHC.Base.>> (do {let {ev_33 = Events.CatEvA (Events.IntEv 3)};
                                                                                                                                        Data.STRef.modifySTRef sref_9 (`Events.deriv` ev_33);
                                                                                                                                        do {acc_34 <- GHC.STRef.readSTRef acc_ref_11;
                                                                                                                                            GHC.STRef.writeSTRef acc_ref_11 (acc_34 GHC.Base.++ [ev_33]);
                                                                                                                                            loop_12}})
                                                                else GHC.STRef.writeSTRef finished_e1_7 GHC.Types.True GHC.Base.>> (do {let {ev_35 = Events.CatPunc};
                                                                                                                                        Data.STRef.modifySTRef sref_9 (`Events.deriv` ev_35);
                                                                                                                                        do {acc_36 <- GHC.STRef.readSTRef acc_ref_11;
                                                                                                                                            GHC.STRef.writeSTRef acc_ref_11 (acc_36 GHC.Base.++ [ev_35]);
                                                                                                                                            loop_12}})}
                                                      else do {intSent_37 <- GHC.STRef.readSTRef intSent_ref_6;
                                                               if GHC.Classes.not intSent_37
                                                                then GHC.STRef.writeSTRef intSent_ref_6 GHC.Types.True GHC.Base.>> (do {let {ev_38 = Events.IntEv 4};
                                                                                                                                        Data.STRef.modifySTRef sref_9 (`Events.deriv` ev_38);
                                                                                                                                        do {acc_39 <- GHC.STRef.readSTRef acc_ref_11;
                                                                                                                                            GHC.STRef.writeSTRef acc_ref_11 (acc_39 GHC.Base.++ [ev_38]);
                                                                                                                                            loop_12}})
                                                                else GHC.STRef.readSTRef acc_ref_11}}
                                            else do {e1_done_40 <- GHC.STRef.readSTRef finished_e1_7;
                                                     if GHC.Classes.not e1_done_40
                                                      then do {intSent_41 <- GHC.STRef.readSTRef intSent_ref_5;
                                                               if GHC.Classes.not intSent_41
                                                                then GHC.STRef.writeSTRef intSent_ref_5 GHC.Types.True GHC.Base.>> (case Events.CatEvA (Events.IntEv 3) of
                                                                                                                                    {Events.CatEvA _ -> loop_12;
                                                                                                                                     Events.CatPunc -> GHC.STRef.writeSTRef seenCatPunc_8 GHC.Types.True GHC.Base.>> loop_12})
                                                                else GHC.STRef.writeSTRef finished_e1_7 GHC.Types.True GHC.Base.>> (case Events.CatPunc of
                                                                                                                                    {Events.CatEvA _ -> loop_12;
                                                                                                                                     Events.CatPunc -> GHC.STRef.writeSTRef seenCatPunc_8 GHC.Types.True GHC.Base.>> loop_12})}
                                                      else do {intSent_42 <- GHC.STRef.readSTRef intSent_ref_6;
                                                               if GHC.Classes.not intSent_42
                                                                then GHC.STRef.writeSTRef intSent_ref_6 GHC.Types.True GHC.Base.>> (case Events.IntEv 4 of
                                                                                                                                    {Events.CatEvA _ -> loop_12;
                                                                                                                                     Events.CatPunc -> GHC.STRef.writeSTRef seenCatPunc_8 GHC.Types.True GHC.Base.>> loop_12})
                                                                else GHC.STRef.readSTRef acc_ref_11}}}}}};
    loop_12}