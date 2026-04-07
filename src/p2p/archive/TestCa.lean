import P2p.Prize3_Complete

#eval List.replicate (2 * 1 - 1) false ++ [true, false]
-- Expected: [false, true, false] since 2*1-1=1

#eval caStepList [false, true, false]
-- Expected: [rule30Local false true false] = [false XOR (true OR false)] = [false XOR true] = [true]

#eval List.replicate (2 * (1 - 1) - 1) false ++ [true, true]
-- 2*(1-1)-1 = 2*0-1 = 0-1 = 0 in Nat (saturating)
-- So replicate 0 false ++ [true,true] = [] ++ [true,true] = [true,true]

#eval 2 * 1 - 1
#eval 2 * (1 - 1) - 1  

#eval List.replicate (2 * 2 - 1) false ++ [true, false]
#eval caStepList (List.replicate (2 * 2 - 1) false ++ [true, false])
#eval List.replicate (2 * (2 - 1) - 1) false ++ [true, true]

def suffix11 (n : Nat) : Fin (2 * n + 1) → Bool :=
  fun i : Fin (2 * n + 1) => decide (i.val = 2 * n - 1 ∨ i.val = 2 * n)

def configToList {n : Nat} (c : Fin (2 * n + 1) → Bool) : List Bool := List.ofFn c

#eval configToList (suffix11 0)
-- suffix11(0) has domain Fin(2*0+1) = Fin 1, so one cell
-- That cell has index 0, and decide(0 = 2*0-1 ∨ 0 = 2*0) = decide(0 = -1 ∨ 0 = 0) = decide(false ∨ true) = true

#eval configToList (suffix11 1)
-- suffix11(1) has domain Fin(3), cells 0,1,2
-- i=0: decide(0=1 ∨ 0=2) = false
-- i=1: decide(1=1 ∨ 1=2) = true
-- i=2: decide(2=1 ∨ 2=2) = true
-- So [false, true, true]

-- Test caStepList_false_true_true for n=1
#eval caStepList (List.replicate (2 * 1 - 1) false ++ [true, true])
-- [false, true, true]
#eval List.replicate (2 * (1 - 1) - 1) false ++ [true, true]
-- [true, true]

-- Test for n=2
#eval caStepList (List.replicate (2 * 2 - 1) false ++ [true, true])
#eval List.replicate (2 * (2 - 1) - 1) false ++ [true, true]
