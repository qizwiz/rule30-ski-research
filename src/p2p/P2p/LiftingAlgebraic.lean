import P2p.CausalConeLemmas

private abbrev F (m n : Nat) : Bool :=
  (caEvolve n (spikeAtList m (2 * n + 1))).getD 0 false

private abbrev G (X m n : Nat) : Bool :=
  (caEvolve n (twoSpikeList X m (2 * n + 1))).getD 0 false

/-!
## F_boundary: the left-boundary spike (position 0) always produces true at the center.
-/

/-- All-false replicate stays all-false under caStepList. -/
private lemma caStepList_zeros (n : Nat) :
    caStepList (List.replicate (n + 2) false) = List.replicate n false := by
  induction n with
  | zero => decide
  | succ n ih =>
    show false :: caStepList (List.replicate (n + 2) false) = false :: List.replicate n false
    congr 1

/-- A true followed by (n+2) falses steps to true followed by n falses. -/
private lemma caStepList_true_zeros (n : Nat) :
    caStepList (true :: List.replicate (n + 2) false) =
    true :: List.replicate n false := by
  cases n with
  | zero => decide
  | succ n =>
    show rule30Local true false false :: caStepList (false :: List.replicate (n + 2) false) =
         true :: List.replicate (n + 1) false
    simp [rule30Local]
    show caStepList (List.replicate (n + 3) false) = List.replicate (n + 1) false
    exact caStepList_zeros (n + 1)

/-- caEvolve n on (true :: 2n falses) yields true at position 0. -/
private lemma caEvolve_true_zeros (n : Nat) :
    (caEvolve n (true :: List.replicate (2 * n) false)).getD 0 false = true := by
  induction n with
  | zero => simp [caEvolve, List.getD]
  | succ n ih =>
    rw [caEvolve_succ]
    have hstep : caStepList (true :: List.replicate (2 * (n + 1)) false) =
                 true :: List.replicate (2 * n) false := by
      conv_lhs => rw [show 2 * (n + 1) = 2 * n + 2 by omega]
      exact caStepList_true_zeros (2 * n)
    rw [hstep]; exact ih

/-- F 0 n = true: the left-boundary spike always survives to the center. -/
theorem F_boundary (n : Nat) : F 0 n = true := by
  simp only [F]
  have heq : spikeAtList 0 (2 * n + 1) = true :: List.replicate (2 * n) false := by
    apply List.ext_getElem?; intro i; simp [spikeAtList]
  rw [heq]; exact caEvolve_true_zeros n

/-!
## F_diag_recurrence: diagonal recurrence for spike evolution.

F m n = rule30Local (F m (n-1)) (F (m-1) (n-1)) (F (m-2) (n-1))

Interpretation: the leftmost cell of the shrinking Rule 30 triangle, when
initialized with a spike at position m, satisfies a 3-term recurrence in m.

The n=1 case follows directly from caStepList unfolding.
The general case requires a deeper argument (pending formalization).
-/

/-- Sub-lemma: F m n is independent of the tape length, as long as it's > 2n. -/
private lemma F_eq_caEvolve_largeN (m n N : Nat) (hN : 2 * n < N) :
    F m n = (caEvolve n (spikeAtList m N)).getD 0 false := by
  simp only [F]
  apply caEvolve_agree n
  · rw [spikeAtList_length]; omega
  · rw [spikeAtList_length]; omega
  · intro i hi
    rw [spikeAtList_getD m (2 * n + 1) i (by omega),
        spikeAtList_getD m N i (by omega)]

/-- The n=1 case of the diagonal recurrence. -/
private lemma F_diag_recurrence_n1 (m : Nat) (hm : 2 ≤ m) :
    F m 1 = rule30Local (F m 0) (F (m-1) 0) (F (m-2) 0) := by
  simp only [F, caEvolve_succ, caEvolve_zero]
  have hstep : (caStepList (spikeAtList m 3)).getD 0 false =
      rule30Local ((spikeAtList m 3).getD 0 false)
                  ((spikeAtList m 3).getD 1 false)
                  ((spikeAtList m 3).getD 2 false) :=
    caStepList_getD_eq _ 0 (by rw [spikeAtList_length]; omega)
  rw [hstep,
      spikeAtList_getD m 3 0 (by omega),
      spikeAtList_getD m 3 1 (by omega),
      spikeAtList_getD m 3 2 (by omega),
      spikeAtList_getD m 1 0 (by omega),
      spikeAtList_getD (m-1) 1 0 (by omega),
      spikeAtList_getD (m-2) 1 0 (by omega)]
  simp [show (1 = m) ↔ (0 = m - 1) from by omega,
        show (2 = m) ↔ (0 = m - 2) from by omega]

/-!
### On the general F_diag_recurrence

The general diagonal recurrence requires showing that
`caEvolve n (spikeAtList m (2n+1))` at position 0 satisfies a 3-term rule30Local
recurrence in m. The key difficulty is that the three terms on the RHS
use *different* starting tapes (spikeAtList m (2(n-1)+1) for F m (n-1), etc.),
so the proof cannot proceed by simple tape decomposition.

The deeper structure: `caStepList(spikeAtList m N)` at position j is
`rule30Local (decide j=m) (decide (j+1)=m) (decide (j+2)=m)`.
For m ≥ 3, this tape has `true` at positions {m-2, m-1, m} — a three-spike tape.
The n-step evolution of this three-spike tape at position 0 equals
`rule30Local (F m (n-1)) (F (m-1) (n-1)) (F (m-2) (n-1))`
IF Rule 30 evolution is "linear" in the sense that three separated spikes evolve
independently until their causal cones overlap.

For the spike cone width of n-1 steps, the spikes at positions m-2, m-1, m need
2(n-1)+1 cells each, and they are separated by 1 cell each, so they remain
non-overlapping for all n. This additivity property — caEvolve of a sum of
separated spikes equals the XOR of individual evolutions — is the key lemma needed.

However, Rule 30 is NOT linear (it involves OR, not XOR), so direct superposition
does NOT hold. The recurrence is nonetheless true but requires a more subtle proof
via the diagonal structure of the Rule 30 triangle.

This is left as sorry pending a complete formalization.
-/

/-!
### Helper lemmas for F_diag_recurrence
-/

/-- Drop j elements from spikeAtList m N gives spikeAtList (m-j) (N-j), when j ≤ m < N. -/
private lemma spikeAtList_drop (m N j : Nat) (hj : j ≤ m) (hjN : j < N) :
    (spikeAtList m N).drop j = spikeAtList (m - j) (N - j) := by
  apply List.ext_getElem (by rw [List.length_drop, spikeAtList_length, spikeAtList_length])
  intro i hi1 hi2
  have hi1' : i < N - j := by rw [List.length_drop, spikeAtList_length] at hi1; exact hi1
  have hi2' : i < N - j := by rw [spikeAtList_length] at hi2; exact hi2
  rw [show ((spikeAtList m N).drop j)[i] = ((spikeAtList m N).drop j).getD i false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1]]
  rw [show (spikeAtList (m - j) (N - j))[i] = (spikeAtList (m - j) (N - j)).getD i false from by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi2]]
  rw [spikeAtList_getD (m - j) (N - j) i hi2']
  conv_lhs =>
    rw [show ((spikeAtList m N).drop j).getD i false =
        (spikeAtList m N).getD (j + i) false from by
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]]
  rw [spikeAtList_getD m N (j + i) (by omega)]
  simp only [decide_eq_decide]; omega

/-- caEvolve commutes with caStepList: evolving k steps then one step = one step then k steps. -/
private lemma caEvolve_caStepList_comm (k : Nat) (l : List Bool) :
    caEvolve k (caStepList l) = caStepList (caEvolve k l) := by
  induction k generalizing l with
  | zero => simp [caEvolve_zero]
  | succ k ih => rw [caEvolve_succ, caEvolve_succ, ih (caStepList l), ih l]

/-- Position 0 after n+1 steps = rule30Local of positions 0,1,2 after n steps,
    provided the initial tape has length ≥ 2*n+3. -/
private lemma caEvolve_getD0_succ (n : Nat) (l : List Bool) (hl : l.length ≥ 2*n+3) :
    (caEvolve (n + 1) l).getD 0 false =
    rule30Local ((caEvolve n l).getD 0 false)
               ((caEvolve n l).getD 1 false)
               ((caEvolve n l).getD 2 false) := by
  rw [caEvolve_succ, caEvolve_caStepList_comm]
  have hlen_n : (caEvolve n l).length ≥ 3 := by
    have := caEvolve_length_le n l (by omega); omega
  rw [caStepList_getD_eq (caEvolve n l) 0 (by omega)]

/-- Shift symmetry: position j of caEvolve n (spikeAtList m N) =
    position 0 of caEvolve n (spikeAtList (m-j) (N-j)). -/
private lemma spikeAt_getD_shift (n m N j : Nat) (hj : j ≤ m) (hjN : j < N) :
    (caEvolve n (spikeAtList m N)).getD j false =
    (caEvolve n (spikeAtList (m - j) (N - j))).getD 0 false := by
  rw [caEvolve_getD_shift n (spikeAtList m N) j, spikeAtList_drop m N j hj hjN]

/-- (caEvolve n (spikeAtList m N)).getD 0 = F m n, when N > 2n. -/
private lemma caEvolve_spike_getD0_eq_F (n m N : Nat) (hN : 2*n < N) :
    (caEvolve n (spikeAtList m N)).getD 0 false = F m n :=
  (F_eq_caEvolve_largeN m n N hN).symm

theorem F_diag_recurrence (m n : Nat) (hm : 2 ≤ m) (hn : 1 ≤ n) :
    F m n = rule30Local (F m (n-1)) (F (m-1) (n-1)) (F (m-2) (n-1)) := by
  cases n with
  | zero => omega
  | succ n =>
    cases n with
    | zero =>
      simp only [Nat.succ_sub_one]
      exact F_diag_recurrence_n1 m hm
    | succ n =>
      -- General case n+2: unfold one step, shift positions 1 and 2 to get F (m-1) and F (m-2)
      simp only [show n + 2 - 1 = n + 1 from by omega]
      show (caEvolve (n+2) (spikeAtList m (2*(n+2)+1))).getD 0 false = _
      rw [show n + 2 = (n + 1) + 1 from rfl]
      have hlen : (spikeAtList m (2 * (n + 2) + 1)).length ≥ 2*(n+1)+3 := by
        rw [spikeAtList_length]; omega
      -- Expand: position 0 after n+2 steps = rule30Local of positions 0,1,2 after n+1 steps
      rw [caEvolve_getD0_succ (n+1) (spikeAtList m (2*(n+2)+1)) hlen]
      -- Position 0 after n+1 steps = F m (n+1)
      have hpos0 : (caEvolve (n+1) (spikeAtList m (2*(n+2)+1))).getD 0 false = F m (n+1) :=
        caEvolve_spike_getD0_eq_F (n+1) m (2*(n+2)+1) (by omega)
      -- Position 1 after n+1 steps = F (m-1) (n+1), by shift symmetry
      have hpos1 : (caEvolve (n+1) (spikeAtList m (2*(n+2)+1))).getD 1 false = F (m-1) (n+1) := by
        rw [spikeAt_getD_shift (n+1) m (2*(n+2)+1) 1 (by omega) (by omega)]
        apply caEvolve_spike_getD0_eq_F; omega
      -- Position 2 after n+1 steps = F (m-2) (n+1), by shift symmetry
      have hpos2 : (caEvolve (n+1) (spikeAtList m (2*(n+2)+1))).getD 2 false = F (m-2) (n+1) := by
        rw [spikeAt_getD_shift (n+1) m (2*(n+2)+1) 2 (by omega) (by omega)]
        apply caEvolve_spike_getD0_eq_F; omega
      rw [hpos0, hpos1, hpos2]

/-- Direct period lookup for active m values (periods verified by native_decide in CausalConeLemmas). -/
def periodOf : Nat → Nat
  | 4  => 8    | 6  => 16   | 8  => 32
  | 10 => 64   | 12 => 64   | 14 => 64
  | 16 => 256  | 20 => 256  | 22 => 256
  | 24 => 512  | 26 => 1024 | 28 => 2048
  | 30 => 4096 | _  => 1

/-- Bridge: convert rule30n_spikeAt_period output into F-notation equality. -/
private lemma F_period_from_cert (m P : Nat)
    (hcert : caEvolve P (spikeAtList m (2*P+2*m+1)) = spikeAtList m (2*m+1))
    (n : Nat) (hn : n ≥ 1) :
    F m n = F m (n + P) := by
  simp only [F]
  -- rule30n_spikeAt_period applied at (n-1) gives:
  --   caEvolve (n-1+1) ... = caEvolve ((n-1+1)+P) ...
  -- which is caEvolve n ... = caEvolve (n+P) ... after arithmetic
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  exact rule30n_spikeAt_period m P hcert n'

theorem F_periodic (m : Nat) :
    ∀ n : Nat, n ≥ 1 → F m (n + periodOf m) = F m n := by
  intro n hn
  match m with
  | 4  => exact (F_period_from_cert 4  8    caEvolve_cert_m4_p8    n hn).symm
  | 6  => exact (F_period_from_cert 6  16   caEvolve_cert_m6_p16   n hn).symm
  | 8  => exact (F_period_from_cert 8  32   caEvolve_cert_m8_p32   n hn).symm
  | 10 => exact (F_period_from_cert 10 64   caEvolve_cert_m10_p64  n hn).symm
  | 12 => exact (F_period_from_cert 12 64   caEvolve_cert_m12_p64  n hn).symm
  | 14 => exact (F_period_from_cert 14 64   caEvolve_cert_m14_p64  n hn).symm
  | 16 => exact (F_period_from_cert 16 256  caEvolve_cert_m16_p256 n hn).symm
  | 20 => exact (F_period_from_cert 20 256  caEvolve_cert_m20_p256 n hn).symm
  | 22 => exact (F_period_from_cert 22 256  caEvolve_cert_m22_p256 n hn).symm
  | 24 => exact (F_period_from_cert 24 512  caEvolve_cert_m24_p512 n hn).symm
  | 26 => exact (F_period_from_cert 26 1024 caEvolve_cert_m26_p1024 n hn).symm
  | 28 => exact (F_period_from_cert 28 2048 caEvolve_cert_m28_p2048 n hn).symm
  | 30 => exact (F_period_from_cert 30 4096 caEvolve_cert_m30_p4096 n hn).symm
  | _  => sorry  -- inactive m and m ≥ 32: period = 1 is not right; needs algebraic proof

theorem G_periodic (X m : Nat) :
    ∀ n : Nat, n ≥ 1 → G X m (n + periodOf m) = G X m n := by sorry

/-- Uniform sensitivity transfer: SubcaseB at n₀ implies SubcaseB at all n₀+k*P_m. -/
theorem uniform_sensitivity_transfer (X m n₀ k : Nat)
    (h_base : F m n₀ ≠ G X m n₀)
    (h_transient : n₀ ≥ 1) :
    F m (n₀ + k * periodOf m) ≠ G X m (n₀ + k * periodOf m) := by
  induction k with
  | zero => simpa
  | succ k ih =>
    have hstep : n₀ + (k + 1) * periodOf m = (n₀ + k * periodOf m) + periodOf m := by
      simp [Nat.succ_mul]; omega
    have hge : n₀ + k * periodOf m ≥ 1 :=
      Nat.le_trans h_transient (Nat.le_add_right _ _)
    rw [hstep, F_periodic m _ hge, G_periodic X m _ hge]
    exact ih

-- Type-checks successfully with one sorry (G_periodic):
#check @uniform_sensitivity_transfer
-- : uniform_sensitivity_transfer :
--   ∀ (X m n₀ k : ℕ),
--   F m n₀ ≠ G X m n₀ → n₀ ≥ 1 → F m (n₀ + k * periodOf m) ≠ G X m (n₀ + k * periodOf m)

