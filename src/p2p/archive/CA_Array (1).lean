/-
CA_Array.lean — Array Bool cellular automaton for fast native_decide
============================================================================

Provides Array Bool versions of caStepList/caEvolve/spikeAtList/twoSpikeLastList,
with equivalence proofs to the List Bool versions in Prize3_Complete.lean.

Motivation: `∀ j : Fin 4096, P j` with List Bool caEvolve takes 94+ CPU minutes
due to linked-list GC pressure. Array Bool (flat, no per-step allocation) is
estimated ~100× faster → under 1 minute for native_decide.

Used to close Sorrys 2 & 3 in SubcaseBPeriod.lean:
  - subcaseB_m28_residue_3class (Fin 2048)
  - subcaseB_m30_residue_unique  (Fin 4096)

Key Lean 4 lemmas used:
  - Array.getElem_toList : xs.toList[i] = xs[i]          (for i < xs.size)
  - Array.length_toList  : xs.toList.length = xs.size
  - Array.toList_ofFn    : (Array.ofFn f).toList = List.ofFn f
  - Array.getElem?_toList : xs.toList[i]? = xs[i]?
  - Array.getD_eq_getD_getElem? : xs.getD i d = xs[i]?.getD d
  - List.getD_eq_getElem?_getD  : List.getD l i d = l[i]?.getD d
-/

import P2p.CausalConeLemmas

/-
================================================================================
SECTION 1: ARRAY BOOL DEFINITIONS
================================================================================
-/

/-- Array-based single CA step: rule30 applied to each triple, shrinks by 2 -/
def caStepArr (a : Array Bool) : Array Bool :=
  if h : 3 ≤ a.size then
    Array.ofFn (fun i : Fin (a.size - 2) =>
      rule30Local (a[i.val]'(by omega))
                  (a[i.val + 1]'(by omega))
                  (a[i.val + 2]'(by omega)))
  else #[]

/-- Array-based CA evolution for n steps -/
def caEvolveArr : Nat → Array Bool → Array Bool
  | 0,     a => a
  | t + 1, a => caEvolveArr t (caStepArr a)

/-- Array Bool spike: true only at position m in [0, N) -/
def spikeArr (m N : Nat) : Array Bool :=
  Array.ofFn (fun k : Fin N => decide (k.val = m))

/-- Array Bool two-spike-last: true at position m and at position N-1 -/
def twoSpikeLastArr (m N : Nat) : Array Bool :=
  Array.ofFn (fun k : Fin N => decide (k.val = m || k.val = N - 1))

/-
================================================================================
SECTION 2: HELPER LEMMAS FOR EQUIVALENCE
================================================================================
-/

/-- `caStepList` getD at in-bounds index i -/
lemma caStepList_getD_val (l : List Bool) (i : Nat) (hi : i + 2 < l.length) :
    (caStepList l).getD i false =
    rule30Local (l.getD i false) (l.getD (i + 1) false) (l.getD (i + 2) false) := by
  induction i generalizing l with
  | zero =>
    match l with
    | [] => simp at hi
    | [_] => simp at hi
    | [_, _] => simp at hi
    | p :: q :: r :: _ => simp [caStepList, List.getD]
  | succ n ih =>
    match l with
    | [] => simp at hi
    | [_] => simp at hi
    | [_, _] => simp at hi; omega
    | p :: q :: r :: rest =>
      simp only [caStepList, List.getD_cons_succ]
      apply ih
      have hlen : (p :: q :: r :: rest).length = (q :: r :: rest).length + 1 := rfl
      omega

/-- Array.getD equals List.getD on toList -/
lemma Array.getD_eq_toList_getD (a : Array Bool) (i : Nat) :
    a.getD i false = a.toList.getD i false := by
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- getD of List.ofFn: in-bounds gives function value, out-of-bounds gives default -/
private lemma List.getD_ofFn_eq {n : Nat} (f : Fin n → Bool) (i : Nat) :
    (List.ofFn f).getD i false = if h : i < n then f ⟨i, h⟩ else false := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split <;> simp

set_option maxHeartbeats 800000 in
/-- caStepArr.toList = caStepList on the same data -/
theorem caStepArr_toList_eq (a : Array Bool) :
    (caStepArr a).toList = caStepList a.toList := by
  by_cases h : 3 ≤ a.size
  · have hal : a.toList.length = a.size := Array.length_toList
    have hstep : (caStepList a.toList).length = a.size - 2 := by
      have := caStep_length a.toList (by omega); omega
    simp only [caStepArr, h, dif_pos, Array.toList_ofFn]
    apply List.ext_getElem
    · simp only [List.length_ofFn]; omega
    · intro i hi1 hi2
      simp only [List.length_ofFn] at hi1
      -- Use getD approach to avoid slow List.getElem_ofFn
      -- LHS: (List.ofFn f)[i]'hi1 → (List.ofFn f).getD i false → f ⟨i, hi1⟩
      conv_lhs => rw [List.getElem_eq_getD false, List.getD_ofFn_eq, dif_pos hi1]
      -- RHS: (caStepList ..)[i]'hi2 → getD → rule30Local
      conv_rhs => rw [List.getElem_eq_getD false, caStepList_getD_val a.toList i (by omega)]
      -- Close: rule30Local a[j]'_ = rule30Local a.toList.getD j false
      simp only [Array.getElem_eq_getD false, Array.getD_eq_toList_getD]
  · push_neg at h
    simp only [caStepArr, show ¬(3 ≤ a.size) from by omega, dif_neg, not_false_eq_true,
               Array.toList_empty]
    have hl : a.toList.length < 3 := by
      have hal : a.toList.length = a.size := Array.length_toList; omega
    match a.toList, hl with
    | [], _ => simp [caStepList]
    | [_], _ => simp [caStepList]
    | [_, _], _ => simp [caStepList]
    | _ :: _ :: _ :: _, h => simp [List.length] at h; omega

/-- Main equivalence: caEvolveArr on toList = caEvolve on same list -/
theorem caEvolveArr_toList_eq (n : Nat) (a : Array Bool) :
    (caEvolveArr n a).toList = caEvolve n a.toList := by
  induction n generalizing a with
  | zero => simp [caEvolveArr, caEvolve]
  | succ n ih =>
    simp only [caEvolveArr, caEvolve]
    rw [ih, caStepArr_toList_eq]

/-- spikeArr.toList = spikeAtList -/
theorem spikeArr_toList_eq (m N : Nat) : (spikeArr m N).toList = spikeAtList m N := by
  simp [spikeArr, spikeAtList, Array.toList_ofFn]

/-- twoSpikeLastArr.toList = twoSpikeLastList -/
theorem twoSpikeLastArr_toList_eq (m N : Nat) :
    (twoSpikeLastArr m N).toList = twoSpikeLastList m N := by
  simp [twoSpikeLastArr, twoSpikeLastList, Array.toList_ofFn]

/-- Array Bool two-spike at arbitrary positions p and q (not necessarily last) -/
def twoSpikeArr (p q N : Nat) : Array Bool :=
  Array.ofFn (fun k : Fin N => decide (k.val = p ∨ k.val = q))

/-- twoSpikeArr.toList = twoSpikeList -/
theorem twoSpikeArr_toList_eq (p q N : Nat) :
    (twoSpikeArr p q N).toList = twoSpikeList p q N := by
  simp [twoSpikeArr, twoSpikeList, Array.toList_ofFn]

/-
================================================================================
SECTION 3: FAST RESIDUE LEMMAS (Array Bool, proved by native_decide)
================================================================================

These are the fast analogues of the sorry'd lemmas in SubcaseBPeriod.lean.
native_decide on Array Bool is ~100× faster than on List Bool:
  - List Bool: 94+ CPU min for Fin 4096 (m=30)
  - Array Bool: estimated < 1 CPU min
-/

set_option maxHeartbeats 4000000000 in
/-- m=28 residue check (fast, Array Bool): fires at j.val+28 ∈ {1293, 1297, 2065}.
    Replaces the sorry in subcaseB_m28_residue_3class. -/
lemma subcaseB_m28_residue_3class_arr :
    ∀ j : Fin 2048,
    (caEvolveArr (j.val + 28 + 1) (spikeArr 28 (2*(j.val+28+1)+1))).toList.getD 0 false = false →
    (caEvolveArr (j.val + 28 + 1) (twoSpikeLastArr 28 (2*(j.val+28+1)+1))).toList.getD 0 false = true →
    j.val + 28 = 1293 ∨ j.val + 28 = 1297 ∨ j.val + 28 = 2065 := by
  native_decide

-- m=30 chunked into 8 × Fin 512 to avoid OOM in native_decide.
-- Firing position j.val+30=4114 (j.val=4084) is in chunk 7 (offset 3584).
set_option maxHeartbeats 400000000 in
private lemma m30_rk0 : ∀ j : Fin 512,
    (caEvolveArr (j.val+30+1) (spikeArr 30 (2*(j.val+30+1)+1))).toList.getD 0 false = false →
    (caEvolveArr (j.val+30+1) (twoSpikeLastArr 30 (2*(j.val+30+1)+1))).toList.getD 0 false = true →
    j.val+30 = 4114 := by native_decide
set_option maxHeartbeats 400000000 in
private lemma m30_rk1 : ∀ j : Fin 512,
    (caEvolveArr (j.val+512+30+1) (spikeArr 30 (2*(j.val+512+30+1)+1))).toList.getD 0 false = false →
    (caEvolveArr (j.val+512+30+1) (twoSpikeLastArr 30 (2*(j.val+512+30+1)+1))).toList.getD 0 false = true →
    j.val+512+30 = 4114 := by native_decide
set_option maxHeartbeats 400000000 in
private lemma m30_rk2 : ∀ j : Fin 512,
    (caEvolveArr (j.val+1024+30+1) (spikeArr 30 (2*(j.val+1024+30+1)+1))).toList.getD 0 false = false →
    (caEvolveArr (j.val+1024+30+1) (twoSpikeLastArr 30 (2*(j.val+1024+30+1)+1))).toList.getD 0 false = true →
    j.val+1024+30 = 4114 := by native_decide
set_option maxHeartbeats 400000000 in
private lemma m30_rk3 : ∀ j : Fin 512,
    (caEvolveArr (j.val+1536+30+1) (spikeArr 30 (2*(j.val+1536+30+1)+1))).toList.getD 0 false = false →
    (caEvolveArr (j.val+1536+30+1) (twoSpikeLastArr 30 (2*(j.val+1536+30+1)+1))).toList.getD 0 false = true →
    j.val+1536+30 = 4114 := by native_decide
set_option maxHeartbeats 400000000 in
private lemma m30_rk4 : ∀ j : Fin 512,
    (caEvolveArr (j.val+2048+30+1) (spikeArr 30 (2*(j.val+2048+30+1)+1))).toList.getD 0 false = false →
    (caEvolveArr (j.val+2048+30+1) (twoSpikeLastArr 30 (2*(j.val+2048+30+1)+1))).toList.getD 0 false = true →
    j.val+2048+30 = 4114 := by native_decide
set_option maxHeartbeats 400000000 in
private lemma m30_rk5 : ∀ j : Fin 512,
    (caEvolveArr (j.val+2560+30+1) (spikeArr 30 (2*(j.val+2560+30+1)+1))).toList.getD 0 false = false →
    (caEvolveArr (j.val+2560+30+1) (twoSpikeLastArr 30 (2*(j.val+2560+30+1)+1))).toList.getD 0 false = true →
    j.val+2560+30 = 4114 := by native_decide
set_option maxHeartbeats 400000000 in
private lemma m30_rk6 : ∀ j : Fin 512,
    (caEvolveArr (j.val+3072+30+1) (spikeArr 30 (2*(j.val+3072+30+1)+1))).toList.getD 0 false = false →
    (caEvolveArr (j.val+3072+30+1) (twoSpikeLastArr 30 (2*(j.val+3072+30+1)+1))).toList.getD 0 false = true →
    j.val+3072+30 = 4114 := by native_decide
set_option maxHeartbeats 400000000 in
private lemma m30_rk7 : ∀ j : Fin 512,
    (caEvolveArr (j.val+3584+30+1) (spikeArr 30 (2*(j.val+3584+30+1)+1))).toList.getD 0 false = false →
    (caEvolveArr (j.val+3584+30+1) (twoSpikeLastArr 30 (2*(j.val+3584+30+1)+1))).toList.getD 0 false = true →
    j.val+3584+30 = 4114 := by native_decide

/-- m=30 residue uniqueness (8×Fin 512 chunks). Replaces sorry in subcaseB_m30_residue_unique. -/
lemma subcaseB_m30_residue_unique_arr :
    ∀ j : Fin 4096,
    (caEvolveArr (j.val+30+1) (spikeArr 30 (2*(j.val+30+1)+1))).toList.getD 0 false = false →
    (caEvolveArr (j.val+30+1) (twoSpikeLastArr 30 (2*(j.val+30+1)+1))).toList.getD 0 false = true →
    j.val+30 = 4114 := by
  intro ⟨v, hv⟩ hF hG
  by_cases h0 : v < 512
  · exact m30_rk0 ⟨v, h0⟩ hF hG
  by_cases h1 : v < 1024
  · have := m30_rk1 ⟨v-512, by omega⟩
      (by convert hF using 5 <;> omega) (by convert hG using 5 <;> omega); omega
  by_cases h2 : v < 1536
  · have := m30_rk2 ⟨v-1024, by omega⟩
      (by convert hF using 5 <;> omega) (by convert hG using 5 <;> omega); omega
  by_cases h3 : v < 2048
  · have := m30_rk3 ⟨v-1536, by omega⟩
      (by convert hF using 5 <;> omega) (by convert hG using 5 <;> omega); omega
  by_cases h4 : v < 2560
  · have := m30_rk4 ⟨v-2048, by omega⟩
      (by convert hF using 5 <;> omega) (by convert hG using 5 <;> omega); omega
  by_cases h5 : v < 3072
  · have := m30_rk5 ⟨v-2560, by omega⟩
      (by convert hF using 5 <;> omega) (by convert hG using 5 <;> omega); omega
  by_cases h6 : v < 3584
  · have := m30_rk6 ⟨v-3072, by omega⟩
      (by convert hF using 5 <;> omega) (by convert hG using 5 <;> omega); omega
  · have := m30_rk7 ⟨v-3584, by omega⟩
      (by convert hF using 5 <;> omega) (by convert hG using 5 <;> omega); omega

/-
================================================================================
SECTION 4: DERIVE ORIGINAL LIST BOOL LEMMAS FROM ARRAY BOOL LEMMAS
================================================================================
-/

set_option maxHeartbeats 800000 in
/-- m=28 residue classification, List Bool form (closes sorry in SubcaseBPeriod.lean) -/
theorem subcaseB_m28_residue_3class_proved :
    ∀ j : Fin 2048,
    (caEvolve (j.val + 28 + 1) (spikeAtList 28 (2*(j.val+28+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 28 + 1) (twoSpikeLastList 28 (2*(j.val+28+1)+1))).getD 0 false = true →
    j.val + 28 = 1293 ∨ j.val + 28 = 1297 ∨ j.val + 28 = 2065 := by
  intro j hF hG
  apply subcaseB_m28_residue_3class_arr j
  · rw [caEvolveArr_toList_eq, spikeArr_toList_eq]; exact hF
  · rw [caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq]; exact hG

set_option maxHeartbeats 800000 in
/-- m=30 residue uniqueness, List Bool form (closes sorry in SubcaseBPeriod.lean) -/
theorem subcaseB_m30_residue_unique_proved :
    ∀ j : Fin 4096,
    (caEvolve (j.val + 30 + 1) (spikeAtList 30 (2*(j.val+30+1)+1))).getD 0 false = false →
    (caEvolve (j.val + 30 + 1) (twoSpikeLastList 30 (2*(j.val+30+1)+1))).getD 0 false = true →
    j.val + 30 = 4114 := by
  intro j hF hG
  apply subcaseB_m30_residue_unique_arr j
  · rw [caEvolveArr_toList_eq, spikeArr_toList_eq]; exact hF
  · rw [caEvolveArr_toList_eq, twoSpikeLastArr_toList_eq]; exact hG

/-
================================================================================
SECTION 5: PERIOD CERTS FOR m=22, w=30, P=32768
(SubcaseBPeriod.lean: subcaseB_m22_ge3087_proved, i≡3 sub-case, j≡0 mod 2)

spike(30) CA orbit period = 4096 (divides 32768).
twoSpike(30,22) CA orbit period = 32768.
Coverage: n' = 19214 + 32768*l (j≡0 mod 2 within i≡3 mod 4 within k≡3 mod 4).
================================================================================
-/

-- Period cert: spike(30) returns to itself after 32768 CA steps
-- N_in = 2*32768+2*30+1 = 65597, N_out = 2*30+1 = 61
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_spike30_p32768 :
    (caEvolveArr 32768 (spikeArr 30 65597)).toList = (spikeArr 30 61).toList := by native_decide

-- Period cert: twoSpike(30,22) returns to itself after 32768 CA steps
-- max(30,22)=30, N_in=65597, N_out=61
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts3022_p32768 :
    (caEvolveArr 32768 (twoSpikeArr 30 22 65597)).toList =
    (twoSpikeArr 30 22 61).toList := by native_decide

-- Base sensitivity: w=30 at n'=19214 (F=false, H=true → F≠H)
-- n_steps=19215, tape=2*19215+1=38431
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m22_base_sens_19214_w30 :
    (caEvolveArr 19215 (spikeArr 30 38431)).toList.getD 0 false ≠
    (caEvolveArr 19215 (twoSpikeArr 30 22 38431)).toList.getD 0 false := by native_decide

/-
================================================================================
SECTION 6: DERIVE LIST BOOL FORMS FOR SUBCASEBPERIOD.LEAN
================================================================================
-/

/-- Period cert: spike(30) P=32768, List Bool form -/
theorem caEvolve_cert_spike30_p32768 :
    caEvolve 32768 (spikeAtList 30 65597) = spikeAtList 30 61 := by
  have h := caEvolveArr_cert_spike30_p32768
  rw [caEvolveArr_toList_eq, spikeArr_toList_eq, spikeArr_toList_eq] at h
  exact h

/-- Period cert: twoSpike(30,22) P=32768, List Bool form -/
theorem caEvolve_cert_ts3022_p32768 :
    caEvolve 32768 (twoSpikeList 30 22 65597) = twoSpikeList 30 22 61 := by
  have h := caEvolveArr_cert_ts3022_p32768
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- Base sensitivity: w=30 at n'=19214, List Bool form -/
theorem subcaseB_m22_base_sens_19214_w30 :
    (caEvolve 19215 (spikeAtList 30 38431)).getD 0 false ≠
    (caEvolve 19215 (twoSpikeList 30 22 38431)).getD 0 false := by
  have h := caEvolveArr_m22_base_sens_19214_w30
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-
================================================================================
SECTION 7: PERIOD CERTS FOR m=22 sub-cases: spike(18)/twoSpike(18,22) P=4096,
           spike(5)/twoSpike(5,22) P=4096
(SubcaseBPeriod.lean: subcaseB_m22_ge3087_proved, i≡3/k≡1 and i≡3/k≡3 sub-cases)

spike(18) CA orbit period = 4096.
twoSpike(18,22) CA orbit period = 4096.
spike(5) CA orbit period = 4096.
twoSpike(5,22) CA orbit period = 4096.
================================================================================
-/

-- Period cert: spike(18) returns to itself after 4096 CA steps
-- N_in = 2*4096+2*18+1=8229, N_out = 2*18+1=37
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_spike18_p4096 :
    (caEvolveArr 4096 (spikeArr 18 8229)).toList = (spikeArr 18 37).toList := by native_decide

-- Period cert: twoSpike(18,22) returns to itself after 4096 CA steps
-- max(18,22)=22, N_in=2*4096+2*22+1=8237, N_out=2*22+1=45
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts1822_p4096 :
    (caEvolveArr 4096 (twoSpikeArr 18 22 8237)).toList =
    (twoSpikeArr 18 22 45).toList := by native_decide

-- Period cert: spike(5) returns to itself after 4096 CA steps
-- N_in = 2*4096+2*5+1=8203, N_out = 2*5+1=11
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_spike5_p4096 :
    (caEvolveArr 4096 (spikeArr 5 8203)).toList = (spikeArr 5 11).toList := by native_decide

-- Period cert: twoSpike(5,22) returns to itself after 4096 CA steps
-- max(5,22)=22, N_in=2*4096+2*22+1=8237, N_out=2*22+1=45
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts522_p4096 :
    (caEvolveArr 4096 (twoSpikeArr 5 22 8237)).toList =
    (twoSpikeArr 5 22 45).toList := by native_decide

/-
================================================================================
SECTION 8: PERIOD CERTS FOR m=22 sub-case i≡3/k≡3: P=16384
           twoSpike(28,22), spike(26), twoSpike(26,22)

spike(26) CA orbit period = 16384.
twoSpike(28,22) CA orbit period = 16384.
twoSpike(26,22) CA orbit period = 16384.
N_in for P=16384:
  spike(28):      N_in=2*16384+2*28+1=32825, N_out=57
  twoSpike(28,22):N_in=2*16384+2*28+1=32825, N_out=57
  spike(26):      N_in=2*16384+2*26+1=32821, N_out=53
  twoSpike(26,22):N_in=2*16384+2*26+1=32821, N_out=53
================================================================================
-/

-- Period cert: twoSpike(28,22) returns to itself after 16384 CA steps
-- max(28,22)=28, N_in=32825, N_out=57
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts2822_p16384 :
    (caEvolveArr 16384 (twoSpikeArr 28 22 32825)).toList =
    (twoSpikeArr 28 22 57).toList := by native_decide

-- Period cert: spike(26) returns to itself after 16384 CA steps
-- N_in=32821, N_out=53
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_spike26_p16384 :
    (caEvolveArr 16384 (spikeArr 26 32821)).toList = (spikeArr 26 53).toList := by native_decide

-- Period cert: twoSpike(26,22) returns to itself after 16384 CA steps
-- max(26,22)=26, N_in=32821, N_out=53
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_cert_ts2622_p16384 :
    (caEvolveArr 16384 (twoSpikeArr 26 22 32821)).toList =
    (twoSpikeArr 26 22 53).toList := by native_decide

/-
================================================================================
SECTION 9: BASE SENSITIVITY LEMMAS FOR m=22 sub-case i≡3 (Array Bool)

w=28 at n''=6926: n_steps=6927, tape=13855
w=26 at n''=11022: n_steps=11023, tape=22047
w=26 at n''=15118: n_steps=15119, tape=30239
================================================================================
-/

-- Base sensitivity: w=28 at n''=6926 (F=false, H=true → F≠H)
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m22_base_sens_6926_w28 :
    (caEvolveArr 6927 (spikeArr 28 13855)).toList.getD 0 false ≠
    (caEvolveArr 6927 (twoSpikeArr 28 22 13855)).toList.getD 0 false := by native_decide

-- Base sensitivity: w=26 at n''=11022 (F=false, H=true → F≠H)
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m22_base_sens_11022_w26 :
    (caEvolveArr 11023 (spikeArr 26 22047)).toList.getD 0 false ≠
    (caEvolveArr 11023 (twoSpikeArr 26 22 22047)).toList.getD 0 false := by native_decide

-- Base sensitivity: w=26 at n''=15118 (F=false, H=true → F≠H)
set_option maxHeartbeats 4000000000 in
lemma caEvolveArr_m22_base_sens_15118_w26 :
    (caEvolveArr 15119 (spikeArr 26 30239)).toList.getD 0 false ≠
    (caEvolveArr 15119 (twoSpikeArr 26 22 30239)).toList.getD 0 false := by native_decide

/-
================================================================================
SECTION 10: DERIVE LIST BOOL FORMS FOR ALL NEW CERTS
================================================================================
-/

/-- Period cert: spike(18) P=4096, List Bool form -/
theorem caEvolve_cert_spike18_p4096 :
    caEvolve 4096 (spikeAtList 18 8229) = spikeAtList 18 37 := by
  have h := caEvolveArr_cert_spike18_p4096
  rw [caEvolveArr_toList_eq, spikeArr_toList_eq, spikeArr_toList_eq] at h
  exact h

/-- Period cert: twoSpike(18,22) P=4096, List Bool form -/
theorem caEvolve_cert_ts1822_p4096 :
    caEvolve 4096 (twoSpikeList 18 22 8237) = twoSpikeList 18 22 45 := by
  have h := caEvolveArr_cert_ts1822_p4096
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- Period cert: spike(5) P=4096, List Bool form -/
theorem caEvolve_cert_spike5_p4096 :
    caEvolve 4096 (spikeAtList 5 8203) = spikeAtList 5 11 := by
  have h := caEvolveArr_cert_spike5_p4096
  rw [caEvolveArr_toList_eq, spikeArr_toList_eq, spikeArr_toList_eq] at h
  exact h

/-- Period cert: twoSpike(5,22) P=4096, List Bool form -/
theorem caEvolve_cert_ts522_p4096 :
    caEvolve 4096 (twoSpikeList 5 22 8237) = twoSpikeList 5 22 45 := by
  have h := caEvolveArr_cert_ts522_p4096
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- Period cert: twoSpike(28,22) P=16384, List Bool form -/
theorem caEvolve_cert_ts2822_p16384 :
    caEvolve 16384 (twoSpikeList 28 22 32825) = twoSpikeList 28 22 57 := by
  have h := caEvolveArr_cert_ts2822_p16384
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- Period cert: spike(26) P=16384, List Bool form -/
theorem caEvolve_cert_spike26_p16384 :
    caEvolve 16384 (spikeAtList 26 32821) = spikeAtList 26 53 := by
  have h := caEvolveArr_cert_spike26_p16384
  rw [caEvolveArr_toList_eq, spikeArr_toList_eq, spikeArr_toList_eq] at h
  exact h

/-- Period cert: twoSpike(26,22) P=16384, List Bool form -/
theorem caEvolve_cert_ts2622_p16384 :
    caEvolve 16384 (twoSpikeList 26 22 32821) = twoSpikeList 26 22 53 := by
  have h := caEvolveArr_cert_ts2622_p16384
  rw [caEvolveArr_toList_eq, twoSpikeArr_toList_eq, twoSpikeArr_toList_eq] at h
  exact h

/-- Base sensitivity: w=28 at n''=6926, List Bool form -/
theorem subcaseB_m22_base_sens_6926_w28 :
    (caEvolve 6927 (spikeAtList 28 13855)).getD 0 false ≠
    (caEvolve 6927 (twoSpikeList 28 22 13855)).getD 0 false := by
  have h := caEvolveArr_m22_base_sens_6926_w28
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-- Base sensitivity: w=26 at n''=11022, List Bool form -/
theorem subcaseB_m22_base_sens_11022_w26 :
    (caEvolve 11023 (spikeAtList 26 22047)).getD 0 false ≠
    (caEvolve 11023 (twoSpikeList 26 22 22047)).getD 0 false := by
  have h := caEvolveArr_m22_base_sens_11022_w26
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h

/-- Base sensitivity: w=26 at n''=15118, List Bool form -/
theorem subcaseB_m22_base_sens_15118_w26 :
    (caEvolve 15119 (spikeAtList 26 30239)).getD 0 false ≠
    (caEvolve 15119 (twoSpikeList 26 22 30239)).getD 0 false := by
  have h := caEvolveArr_m22_base_sens_15118_w26
  rwa [caEvolveArr_toList_eq, spikeArr_toList_eq,
       caEvolveArr_toList_eq, twoSpikeArr_toList_eq] at h
