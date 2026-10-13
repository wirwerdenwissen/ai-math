module

public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Size
public import Results.Pairing.SquareStage.Harmonic

/-!
# Power-sum evaluation of square-stage quotas

- **Claim:** a recursive power-sum table evaluates the concrete harmonic
  approximation exactly, with polynomial bounds for the explicitly defined
  work counters and a quadratic bound on a common denominator's bit length.
- **Main declaration:** `SquareStagePairing.PowerSums.quota_table_correct`,
  `SquareStagePairing.PowerSums.harmonic_work_bound`, and
  `SquareStagePairing.PowerSums.harmonic_den_bits`.
- **Not proved:** a compiler cost theorem, a bound on every intermediate
  numerator, or the complete bit complexity of pairing and unpairing.
  The work counters below are explicit arithmetic/list-work models, not
  a formal operational semantics of the evaluator.
- **Author:** avocardio (human), with OpenAI Codex (GPT family).

The power-sum recurrence is the usual telescoping consequence of the
binomial theorem. No novelty is asserted for that recurrence.
-/

@[expose] public section

namespace SquareStagePairing.PowerSums
open Finset
open scoped BigOperators

def powerSum (n r : ℕ) : ℚ := ∑ k ∈ range n, (k : ℚ) ^ r

theorem power_sum_succ (n r : ℕ) :
    powerSum (n + 1) r = powerSum n r + (n : ℚ) ^ r := by
  exact sum_range_succ _ _

theorem power_sum_recurrence (n r : ℕ) :
    (r + 1 : ℚ) * powerSum n r = (n : ℚ) ^ (r + 1) -
      ∑ i ∈ range r, (Nat.choose (r + 1) i : ℚ) * powerSum n i := by
  induction n with
  | zero => simp [powerSum]
  | succ n ih =>
    have hb := add_pow (n : ℚ) 1 (r + 1)
    simp only [one_pow, mul_one, sum_range_succ, Nat.choose_self, Nat.cast_one,
      Nat.choose_succ_self_right, Nat.cast_add] at hb
    have hs : (∑ i ∈ range r, (n : ℚ) ^ i * (Nat.choose (r + 1) i : ℚ)) =
        ∑ i ∈ range r, (Nat.choose (r + 1) i : ℚ) * (n : ℚ) ^ i := by
      apply sum_congr rfl
      intro i _
      ring
    rw [hs] at hb
    rw [power_sum_succ]
    simp_rw [power_sum_succ, mul_add, sum_add_distrib]
    push_cast
    nlinarith [hb]

theorem power_sum_evaluate (n r : ℕ) :
    powerSum n r = ((n : ℚ) ^ (r + 1) -
      ∑ i ∈ range r, (Nat.choose (r + 1) i : ℚ) * powerSum n i) / (r + 1 : ℚ) := by
  apply (eq_div_iff (by positivity : (r + 1 : ℚ) ≠ 0)).2
  simpa only [mul_comm] using power_sum_recurrence n r

theorem power_sum_interval {a b : ℕ} (hab : a ≤ b) (r : ℕ) :
    (∑ k ∈ Ico a b, (k : ℚ) ^ r) = powerSum b r - powerSum a r := by
  exact sum_Ico_eq_sub _ hab

def centeredMoment (a b r : ℕ) : ℚ :=
  ∑ i ∈ range (r + 1), (Nat.choose r i : ℚ) * 2 ^ i * (-(3 * (a : ℚ))) ^ (r - i) *
    (powerSum b i - powerSum a i)

theorem centered_moment_evaluate {a b : ℕ} (hab : a ≤ b) (r : ℕ) :
    (∑ k ∈ Ico a b, (2 * (k : ℚ) - 3 * a) ^ r) = centeredMoment a b r := by
  unfold centeredMoment
  simp_rw [show ∀ k : ℕ, (2 * (k : ℚ) - 3 * a) ^ r =
      (2 * (k : ℚ) + -(3 * a)) ^ r by intro k; rw [sub_eq_add_neg], add_pow, mul_pow]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _hi
  rw [← power_sum_interval hab]
  rw [mul_sum]
  apply sum_congr rfl
  intro k _hk
  ring

def blockEval (a b P : ℕ) : ℚ :=
  ∑ r ∈ range (P + 1), 2 * (-1 : ℚ) ^ r * centeredMoment a b r / (3 * a : ℚ) ^ (r + 1)

theorem geometric_coefficient (a k : ℚ) (ha : a ≠ 0) (r : ℕ) :
    2 / (3 * a) * ((3 * a - 2 * k) / (3 * a)) ^ r =
      2 * (-1 : ℚ) ^ r * (2 * k - 3 * a) ^ r / (3 * a) ^ (r + 1) := by
  have hn : 3 * a - 2 * k = -(2 * k - 3 * a) := by ring
  rw [hn, div_pow, neg_pow, pow_succ]
  field_simp

theorem block_evaluate {a b P : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ k ∈ Ico a b, SquareStagePairing.Harmonic.term a k P) = blockEval a b P := by
  unfold SquareStagePairing.Harmonic.term blockEval
  simp_rw [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro r _hr
  rw [← centered_moment_evaluate hab]
  rw [mul_sum]
  simp_rw [div_eq_mul_inv]
  rw [sum_mul]
  apply sum_congr rfl
  intro k _hk
  simpa only [div_eq_mul_inv] using
    geometric_coefficient a k (by exact_mod_cast Nat.ne_of_gt ha) r

def chooseEval (n k : ℕ) : ℕ :=
  if k ≤ n then n.factorial / (k.factorial * (n - k).factorial) else 0

theorem choose_eval_correct (n k : ℕ) : chooseEval n k = Nat.choose n k := by
  unfold chooseEval
  split_ifs with h
  · exact (Nat.choose_eq_factorial_div_factorial h).symm
  · exact (Nat.choose_eq_zero_of_lt (by omega)).symm

def powerTable (n : ℕ) : ℕ → List ℚ
  | 0 => []
  | r + 1 =>
    let previous := powerTable n r
    previous ++ [((n : ℚ) ^ (r + 1) -
      ∑ i ∈ range r, (chooseEval (r + 1) i : ℚ) * previous.getD i 0) / (r + 1 : ℚ)]

theorem power_table_length (n r : ℕ) : (powerTable n r).length = r := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [powerTable, List.length_append, List.length_singleton, ih]

theorem power_table_correct (n r i : ℕ) (hi : i < r) :
    (powerTable n r).getD i 0 = powerSum n i := by
  induction r generalizing i with
  | zero => omega
  | succ r ih =>
    rw [powerTable]
    by_cases hir : i < r
    · rw [List.getD_append _ _ _ _ (by simpa [power_table_length] using hir)]
      exact ih i hir
    · have hieq : i = r := by omega
      subst i
      rw [List.getD_append_right _ _ _ _ (by simp [power_table_length])]
      simp only [power_table_length, Nat.sub_self, List.getD_cons_zero, choose_eval_correct]
      have hs : (∑ i ∈ range r, (Nat.choose (r + 1) i : ℚ) *
          (powerTable n r).getD i 0) =
          ∑ i ∈ range r, (Nat.choose (r + 1) i : ℚ) * powerSum n i := by
        apply sum_congr rfl
        intro i hi
        rw [ih i (mem_range.mp hi)]
      rw [hs]
      exact (power_sum_evaluate n r).symm

def blockTableEval (a b P : ℕ) : ℚ :=
  let low := powerTable a (P + 1)
  let high := powerTable b (P + 1)
  ∑ r ∈ range (P + 1), 2 * (-1 : ℚ) ^ r *
    (∑ i ∈ range (r + 1), (chooseEval r i : ℚ) * 2 ^ i * (-(3 * (a : ℚ))) ^ (r - i) *
      (high.getD i 0 - low.getD i 0)) / (3 * a : ℚ) ^ (r + 1)

theorem block_table_correct (a b P : ℕ) : blockTableEval a b P = blockEval a b P := by
  unfold blockTableEval blockEval centeredMoment
  simp only [choose_eval_correct]
  apply sum_congr rfl
  intro r hr
  congr 2
  apply sum_congr rfl
  intro i hi
  have hir : i < P + 1 := by
    simp only [mem_range] at hr hi
    omega
  rw [power_table_correct _ _ _ hir, power_table_correct _ _ _ hir]

theorem block_table_evaluate {a b P : ℕ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ k ∈ Ico a b, SquareStagePairing.Harmonic.term a k P) = blockTableEval a b P := by
  rw [block_table_correct]
  exact block_evaluate ha hab

def truncatedBlockEval (a m P : ℕ) : ℚ :=
  if a ≤ m then blockTableEval a (min (2 * a) (m + 1)) P else 0

theorem truncated_block_correct {a m P : ℕ} (ha : 0 < a) :
    truncatedBlockEval a m P = SquareStagePairing.Harmonic.blockApprox a m P := by
  unfold truncatedBlockEval SquareStagePairing.Harmonic.blockApprox SquareStagePairing.Harmonic.block
  split_ifs with ham
  · rw [min_eq_left (by omega : a ≤ m + 1)]
    exact (block_table_evaluate ha (by omega)).symm
  · have h1 : min a (m + 1) = m + 1 := min_eq_right (by omega)
    have h2 : min (2 * a) (m + 1) = m + 1 := min_eq_right (by omega)
    rw [h1, h2]
    simp

def harmonicTable (L m : ℕ) : ℚ :=
  if m = 0 then 0 else if m = 1 then 1 else
    ∑ b ∈ range L, truncatedBlockEval (2 ^ b) m (4 * L + 4)

theorem harmonic_table_correct (L m : ℕ) :
    harmonicTable L m = SquareStagePairing.Harmonic.harmonicApprox L m := by
  unfold harmonicTable SquareStagePairing.Harmonic.harmonicApprox SquareStagePairing.Harmonic.rawApprox
  split_ifs
  · rfl
  · rfl
  · apply sum_congr rfl
    intro b _
    exact truncated_block_correct (by positivity)

def quotaTable (L j m : ℕ) : ℤ :=
  ⌊2 * (j : ℚ) ^ 2 * harmonicTable L m - (m : ℚ) ^ 2⌋

theorem quota_table_correct (L j m : ℕ) : quotaTable L j m = SquareStagePairing.Harmonic.quota L j m := by
  unfold quotaTable SquareStagePairing.Harmonic.quota SquareStagePairing.Harmonic.approx
  rw [harmonic_table_correct]

/- Conservative arithmetic/list-work model. These counters bound the explicit
   loops when powers and factorials use repeated multiplication. They are not a
   theorem about the Lean compiler or about unit-cost unbounded integers. -/
def tableWork : ℕ → ℕ
  | 0 => 0
  | r + 1 => tableWork r + (4 * r + 11) * r + 2 * r + 4

theorem table_work_bound (r : ℕ) : tableWork r ≤ 20 * (r + 1) ^ 3 := by
  induction r with
  | zero => norm_num [tableWork]
  | succ r ih =>
    rw [tableWork]
    nlinarith

def blockWork (P : ℕ) : ℕ :=
  2 * tableWork (P + 1) + (P + 1) ^ 2 * (7 * P + 12) + (P + 1) * (2 * P + 8)

theorem block_work_bound (P : ℕ) : blockWork P ≤ 100 * (P + 2) ^ 3 := by
  have h := table_work_bound (P + 1)
  unfold blockWork
  nlinarith

def harmonicWork (L : ℕ) : ℕ := L * (blockWork (4 * L + 4) + L + 10) + 10

theorem harmonic_work_bound (L : ℕ) : harmonicWork L ≤ 100000 * (L + 2) ^ 4 := by
  have h := block_work_bound (4 * L + 4)
  have hm := Nat.mul_le_mul_left L h
  unfold harmonicWork
  nlinarith

def commonDen (L P : ℕ) : ℕ := 3 ^ (P + 1) * 2 ^ ((L - 1) * (P + 1))

theorem local_denominator_divides {L P b r : ℕ} (hb : b < L) (hr : r ≤ P) :
    (3 * 2 ^ b) ^ (r + 1) ∣ commonDen L P := by
  have hb' : b ≤ L - 1 := by omega
  have hbase : 3 * 2 ^ b ∣ 3 * 2 ^ (L - 1) :=
    Nat.mul_dvd_mul_left 3 (pow_dvd_pow 2 hb')
  have h1 : (3 * 2 ^ b) ^ (r + 1) ∣ (3 * 2 ^ b) ^ (P + 1) :=
    pow_dvd_pow _ (by omega)
  have h2 := pow_dvd_pow_of_dvd hbase (P + 1)
  have heq : (3 * 2 ^ (L - 1)) ^ (P + 1) = commonDen L P := by
    simp only [commonDen, mul_pow, pow_mul]
  exact heq ▸ dvd_trans h1 h2

theorem common_den_lt_pow {L P : ℕ} (hL : 0 < L) :
    commonDen L P < 2 ^ ((L + 1) * (P + 1)) := by
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
  have hbase : 3 * 2 ^ l < 2 ^ (l + 2) := by
    rw [pow_add]
    norm_num
    have hp : 0 < 2 ^ l := by positivity
    nlinarith
  calc
    commonDen (l + 1) P = (3 * 2 ^ l) ^ (P + 1) := by
      simp only [commonDen, Nat.add_sub_cancel, mul_pow, pow_mul]
    _ < (2 ^ (l + 2)) ^ (P + 1) :=
      pow_lt_pow_left₀ hbase (Nat.zero_le _) (Nat.succ_ne_zero P)
    _ = 2 ^ ((l + 1 + 1) * (P + 1)) := by rw [← pow_mul]

theorem common_den_bits {L P : ℕ} (hL : 0 < L) :
    Nat.size (commonDen L P) ≤ (L + 1) * (P + 1) :=
  Nat.size_le.mpr (common_den_lt_pow hL)

theorem harmonic_den_bits {L : ℕ} (hL : 0 < L) :
    Nat.size (commonDen L (4 * L + 4)) ≤ 5 * (L + 1) ^ 2 := by
  have h := common_den_bits (P := 4 * L + 4) hL
  nlinarith

end SquareStagePairing.PowerSums
