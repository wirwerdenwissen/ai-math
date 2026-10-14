module

public import Results.Pairing.SquareStage.Harmonic
public import Results.Pairing.SquareStage.PowerSums
public import Results.Pairing.SquareStage.Search
public import Mathlib.NumberTheory.Harmonic.Defs

/-!
# A concrete dyadic square-stage pairing

- **Claim:** the executable square-stage maps are mutual inverses and cover
  every pair in a product-bounded region by the specified stage.
- **Main declaration:** `SquareStagePairing.Concrete.pairingEquiv`,
  `SquareStagePairing.Concrete.product_coverage`.
- **Not proved:** a complete bit-complexity theorem or two-sided localization;
  the waste bound is proved separately in `Results.Pairing.SquareStage.Final`.
- **Author:** avocardio (human); OpenAI Codex (GPT family).

The inputs `(x, y)` encode the positive pair `(x + 1, y + 1)`.
The dyadic harmonic evaluator supplies all approximation and quota hypotheses
required by the generic stage and binary-search modules.
-/

@[expose] public section

namespace SquareStagePairing.Concrete
open SquareStagePairing.Harmonic SquareStagePairing.Bijection

def rowTable (L j m : ℕ) : ℤ :=
  SquareStagePairing.PowerSums.quotaTable L j m - SquareStagePairing.PowerSums.quotaTable L j (m - 1)

theorem rowTable_eq (L j m : ℕ) : rowTable L j m = rowQuota L j m := by
  simp only [rowTable, SquareStagePairing.PowerSums.quota_table_correct, rowQuota]

def rowZ (j m : ℕ) : ℤ :=
  if m < j then rowTable j.size j (m + 1) else 0
def row (j m : ℕ) : ℕ := (rowZ j m).toNat
def cumulativeZ (j m : ℕ) : ℤ := SquareStagePairing.PowerSums.quotaTable j.size j (min m j)
def cumulative (j m : ℕ) : ℕ := (cumulativeZ j m).toNat

theorem rowZ_nonnegative (j m : ℕ) : 0 ≤ rowZ j m := by
  unfold rowZ
  simp only [rowTable_eq]
  split
  · exact row_quota_nonnegative (Nat.lt_size_self j) (by omega) (by omega)
  · omega

theorem row_cast (j m : ℕ) : (row j m : ℤ) = rowZ j m :=
  Int.toNat_of_nonneg (rowZ_nonnegative j m)

theorem row_support (j m : ℕ) (h : j ≤ m) : row j m = 0 := by
  simp [row, rowZ, show ¬ m < j by omega]

theorem row_growth (j m : ℕ) (h : m < j) : row j m + 2 ≤ row (j + 1) m := by
  have hg := row_quota_growth (Nat.lt_size_self j) (Nat.lt_size_self (j + 1))
    (show 0 < m + 1 by omega) (show m + 1 ≤ j by omega)
  have h0 : rowZ j m = rowQuota j.size j (m + 1) := by simp [rowZ, h, rowTable_eq]
  have h1 : rowZ (j + 1) m = rowQuota (j + 1).size (j + 1) (m + 1) := by
    simp [rowZ, rowTable_eq, show m < j + 1 by omega]
  rw [← h0, ← h1, ← row_cast, ← row_cast] at hg
  exact_mod_cast hg

def quotas : Quotas := quotasFromGrowth row row_support row_growth

theorem quota_nonnegative (j m : ℕ) (hm : m ≤ j) : 0 ≤ quota j.size j m := by
  induction m with
  | zero => rw [quota_zero]
  | succ m ih =>
    have hp := ih (by omega)
    have hr := row_quota_nonnegative (Nat.lt_size_self j)
      (show 0 < m + 1 by omega) hm
    simp only [rowQuota, Nat.add_sub_cancel] at hr
    omega

theorem cumulative_cast (j m : ℕ) : (cumulative j m : ℤ) = cumulativeZ j m := by
  apply Int.toNat_of_nonneg
  simp only [cumulativeZ, SquareStagePairing.PowerSums.quota_table_correct]
  exact quota_nonnegative j (min m j) (Nat.min_le_right _ _)

theorem cumulative_zero (j : ℕ) : cumulative j 0 = 0 := by
  simp [cumulative, cumulativeZ, SquareStagePairing.PowerSums.quota_table_correct, quota_zero]

theorem cumulative_step (j m : ℕ) : cumulative j (m + 1) = cumulative j m + row j m := by
  by_cases hm : m < j
  · have hcast0 := cumulative_cast j m
    have hcast1 := cumulative_cast j (m + 1)
    have hrow := row_cast j m
    simp only [cumulativeZ, SquareStagePairing.PowerSums.quota_table_correct,
      min_eq_left (show m ≤ j by omega)] at hcast0
    simp only [cumulativeZ, SquareStagePairing.PowerSums.quota_table_correct,
      min_eq_left (show m + 1 ≤ j by omega)] at hcast1
    simp only [rowZ, ite_eq_left hm, rowTable_eq, rowQuota, Nat.add_sub_cancel] at hrow
    omega
  · have hjm : j ≤ m := by omega
    have hjm1 : j ≤ m + 1 := by omega
    simp [cumulative, cumulativeZ, min_eq_right hjm, min_eq_right hjm1,
      row_support j m hjm]

def cumulativeQuotas : Cumulative quotas where
  Q := cumulative
  zero := cumulative_zero
  step := cumulative_step

theorem total_cast (j : ℕ) : (total quotas j : ℤ) = quota j.size j j := by
  have ht := fastTotal_eq quotas cumulativeQuotas j
  change cumulative j j = total quotas j at ht
  have hc := cumulative_cast j j
  rw [← ht]
  simpa [cumulativeZ, SquareStagePairing.PowerSums.quota_table_correct] using hc

theorem total_le_ideal (j : ℕ) : (total quotas j : ℚ) ≤ SquareStagePairing.Harmonic.ideal j j + 1 := by
  have he := (quota_error (Nat.lt_size_self j) (Nat.le_refl j)).2
  have hc := total_cast j
  have hcQ : (total quotas j : ℚ) = (quota j.size j j : ℚ) := by exact_mod_cast hc
  linarith

theorem harmonic_eq_standard (j : ℕ) : SquareStagePairing.Harmonic.harmonic j = _root_.harmonic j := by
  induction j with
  | zero => simp [SquareStagePairing.Harmonic.harmonic_zero]
  | succ j ih =>
    rw [SquareStagePairing.Harmonic.harmonic_succ, _root_.harmonic_succ, ih]
    simp [one_div]

def forward (p : ℕ × ℕ) : ℕ := fastRank quotas cumulativeQuotas (rowEncode p)
def inverse (z : ℕ) : ℕ × ℕ := rowDecode (fastUnrank quotas cumulativeQuotas z)

theorem inverse_forward (p : ℕ × ℕ) : inverse (forward p) = p := by
  simp only [inverse, forward, fastUnrank_fastRank, rowDecode_encode]

theorem forward_inverse (z : ℕ) : forward (inverse z) = z := by
  simp only [inverse, forward, rowEncode_decode, fastRank_fastUnrank]

def pairingEquiv : (ℕ × ℕ) ≃ ℕ where
  toFun := forward
  invFun := inverse
  left_inv := inverse_forward
  right_inv := forward_inverse

theorem product_floor_bound (j u v : ℕ) (hu : 0 < u) (hp : u * v ≤ j ^ 2) :
    (v : ℤ) ≤ ⌊(j : ℚ) ^ 2 / u⌋ := by
  apply Int.le_floor.mpr
  norm_cast
  apply (le_div_iff₀ (by exact_mod_cast hu : (0 : ℚ) < u)).mpr
  push_cast
  have hpQ : (u : ℚ) * v ≤ (j : ℚ) ^ 2 := by exact_mod_cast hp
  nlinarith

theorem row_of_product_bound (x y j : ℕ) (hp : (x + 1) * (y + 1) ≤ j ^ 2) :
    (rowEncode (x, y)).1 + 1 ≤ j ∧
    ((rowEncode (x, y)).2 : ℤ) < actualRow j ((rowEncode (x, y)).1 + 1) := by
  by_cases hxy : x < y
  · have hm : x + 1 ≤ j := by nlinarith
    have hf := product_floor_bound j (x + 1) (y + 1) (by omega) hp
    simp only [rowEncode, ite_eq_left hxy]
    constructor
    · exact hm
    · unfold actualRow
      push_cast at *
      omega
  · have hm : y + 1 ≤ j := by nlinarith
    have hp' : (y + 1) * (x + 1) ≤ j ^ 2 := by nlinarith
    have hf := product_floor_bound j (y + 1) (x + 1) (by omega) hp'
    simp only [rowEncode, ite_eq_right hxy]
    constructor
    · exact hm
    · unfold actualRow
      push_cast at *
      omega

theorem square_coverage (p : ℕ × ℕ) (j : ℕ)
    (hp : (p.1 + 1) * (p.2 + 1) ≤ j ^ 2) : forward p < total quotas (j + 1) := by
  rcases p with ⟨x, y⟩
  obtain ⟨hm, hk⟩ := row_of_product_bound x y j hp
  have hc := next_row_covers (Nat.lt_size_self (j + 1))
    (show 0 < (rowEncode (x, y)).1 + 1 by omega) hm
  have hr := row_cast (j + 1) (rowEncode (x, y)).1
  simp only [rowZ, rowTable_eq, ite_eq_left (show (rowEncode (x, y)).1 < j + 1 by omega)] at hr
  have hkr : (rowEncode (x, y)).2 < row (j + 1) (rowEncode (x, y)).1 := by omega
  simp only [forward, fastRank_eq]
  exact (prefix_characterization quotas (j + 1) (rowEncode (x, y)).1 (rowEncode (x, y)).2).mpr hkr

theorem product_coverage (p : ℕ × ℕ) (A : ℕ)
    (hp : (p.1 + 1) * (p.2 + 1) ≤ A) :
    forward p < total quotas (Nat.sqrt A + 2) := by
  have hA := Nat.lt_succ_sqrt' A
  simp only [Nat.succ_eq_add_one] at hA
  have hs : (p.1 + 1) * (p.2 + 1) ≤ (Nat.sqrt A + 1) ^ 2 := by omega
  have h := square_coverage p (Nat.sqrt A + 1) hs
  simpa only [Nat.add_assoc] using h

end SquareStagePairing.Concrete
