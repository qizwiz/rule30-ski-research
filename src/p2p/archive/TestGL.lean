import P2p.Prize3_Complete
import P2p.LiftingLemma_LeftPermutive

-- Key helper: caStepList propagation for T followed by odd F's
-- caStepList (B ++ [T] ++ [F]^(2j+3)) = caStepList (B ++ [T, F]) ++ [T] ++ [F]^(2j+1)
lemma caStepList_T_oddF_step (j : Nat) (B : List Bool) :
    caStepList (B ++ [true] ++ List.replicate (2 * j + 3) false) =
    caStepList (B ++ [true, false]) ++ [true] ++ List.replicate (2 * j + 1) false := by
  induction j with
  | zero =>
    -- caStepList (B ++ [T, F, F, F]) = caStepList (B ++ [T, F]) ++ [T, F]
    have h : B ++ [true] ++ List.replicate 3 false = B ++ [true, false] ++ [false, false] := by
      simp [List.append_assoc]
    rw [h]
    -- Now use caStepList_append_two_false y=true x=false c=false:
    -- caStepList((B++[T,F]) ++ [false, false, false, false])...
    -- Hmm: we have (B++[T,F]) ++ [F,F] not (M ++ [y, x, c, false])
    -- Need last 4 elements to be [y, x, c, false]:
    -- B ++ [T, F, F, F] = (B ++ [T]) ++ [F, F, F, F]? No, [T, F, F, F] has 4 elements
    -- So B ++ [T, F, F, F] = (B) ++ [T, F, F, F] where y=T, x=F, c=F, last=F
    -- caStepList_append_two_false T F F B :
    -- caStepList(B ++ [T, F, F, false]) = caStepList(B ++ [T, F]) ++ [rule30Local T F F, F ^^ F]
    --                                    = caStepList(B ++ [T, F]) ++ [true, false]
    rw [show B ++ [true, false] ++ [false, false] = B ++ [true, false, false, false] from by simp [List.append_assoc]]
    exact caStepList_append_two_false true false false B
  | succ j ih =>
    -- caStepList (B ++ [T] ++ [F]^(2j+5)) = caStepList (B ++ [T, F]) ++ [T] ++ [F]^(2j+3)
    -- B ++ [T] ++ [F]^(2j+5) = (B ++ [T] ++ [F]^(2j+3)) ++ [F, F]
    have h1 : B ++ [true] ++ List.replicate (2 * (j + 1) + 3) false =
              (B ++ [true] ++ List.replicate (2 * j + 3) false) ++ [false, false] := by
      simp [List.append_assoc, List.replicate_add]
    rw [h1]
    -- caStepList((B++[T]++[F]^(2j+3)) ++ [F, F]):
    -- Last 4 of (B++[T]++[F]^(2j+3)) ++ [F, F] are [F, F, F, F]
    -- Use caStepList_append_two_false y=F x=F c=F:
    -- caStepList(M' ++ [F, F, F, F]) = caStepList(M' ++ [F, F]) ++ [F, F]
    -- where M' = B ++ [T] ++ [F]^(2j+1)
    have h2 : (B ++ [true] ++ List.replicate (2 * j + 3) false) ++ [false, false] =
              (B ++ [true] ++ List.replicate (2 * j + 1) false) ++ [false, false, false, false] := by
      simp [List.append_assoc, List.replicate_add]
    rw [h2, caStepList_append_two_false false false false (B ++ [true] ++ List.replicate (2 * j + 1) false)]
    simp only [rule30Local, Bool.false_xor]
    -- Now: caStepList(B ++ [T] ++ [F]^(2j+1) ++ [F, F]) ++ [F, F]
    --    = (caStepList(B ++ [T, F]) ++ [T] ++ [F]^(2j+1)) ++ [F, F]   by IH
    --    = caStepList(B ++ [T, F]) ++ [T] ++ [F]^(2j+3)
    rw [show (B ++ [true] ++ List.replicate (2 * j + 1) false) ++ [false, false] =
            B ++ [true] ++ List.replicate (2 * j + 3) false from by
          simp [List.append_assoc, List.replicate_add]]
    rw [ih]
    simp [List.append_assoc, List.replicate_add]

