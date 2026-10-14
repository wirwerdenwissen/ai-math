module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Certified harmonic approximations and square-stage quotas

- **Claim:** a concrete rational dyadic-geometric approximation gives a
  cumulative square-stage quota within `17 / 16` of its ideal value, with
  nonnegative row quotas and the growth needed for nested stages.
- **Main declaration:** `SquareStagePairing.Harmonic.approximation_certificate`,
  `SquareStagePairing.Harmonic.quota_error`, and
  `SquareStagePairing.Harmonic.row_quota_growth`.
- **Not proved:** evaluation complexity or the complete pairing theorem.
  The finite sums here specify the approximation; a power-sum evaluator is
  verified separately in `Results.Pairing.SquareStage.PowerSums`.
- **Author:** avocardio (human), with OpenAI Codex (GPT family).

The reciprocal approximation uses the finite geometric series centered on
each dyadic block. Its error estimate is elementary; no literature novelty
is asserted for that approximation.
-/
@[expose] public section

namespace SquareStagePairing.Harmonic
open Finset
open scoped BigOperators

def term (a k : ℚ) (P : ℕ) : ℚ :=
  2 / (3 * a) * ∑ r ∈ range (P + 1), ((3 * a - 2 * k) / (3 * a)) ^ r

theorem term_error_identity {a k : ℚ} (ha : a ≠ 0) (hk : k ≠ 0) (P : ℕ) :
    term a k P - 1 / k = -(((3 * a - 2 * k) / (3 * a)) ^ (P + 1)) / k := by
  have h := geom_sum_mul_neg ((3 * a - 2 * k) / (3 * a)) (P + 1)
  have hz : 1 - (3 * a - 2 * k) / (3 * a) = 2 * k / (3 * a) := by
    field_simp
    ring
  rw [hz] at h
  have ht : term a k P * k = 1 - ((3 * a - 2 * k) / (3 * a)) ^ (P + 1) := by
    unfold term
    calc
      2 / (3 * a) * (∑ r ∈ range (P + 1), ((3 * a - 2 * k) / (3 * a)) ^ r) * k
        = (∑ r ∈ range (P + 1), ((3 * a - 2 * k) / (3 * a)) ^ r) *
            (2 * k / (3 * a)) := by ring
      _ = _ := h
  apply (eq_div_iff hk).2
  rw [sub_mul]
  have hinv : (1 / k) * k = 1 := by field_simp
  rw [hinv, ht]
  ring

theorem term_error {a k : ℚ} (ha : 0 < a) (hak : a ≤ k) (hka : k ≤ 2 * a)
    (P : ℕ) : |term a k P - 1 / k| ≤ 1 / (a * 3 ^ (P + 1)) := by
  have hk : 0 < k := lt_of_lt_of_le ha hak
  have hratio : |(3 * a - 2 * k) / (3 * a)| ≤ (1 : ℚ) / 3 := by
    rw [abs_le]
    constructor
    · apply (le_div_iff₀ (by positivity : 0 < 3 * a)).2
      linarith
    · apply (div_le_iff₀ (by positivity : 0 < 3 * a)).2
      linarith
  rw [term_error_identity (ne_of_gt ha) (ne_of_gt hk), abs_div, abs_neg, abs_pow,
    abs_of_pos hk]
  have hp := pow_le_pow_left₀ (abs_nonneg ((3 * a - 2 * k) / (3 * a))) hratio (P + 1)
  calc
    |(3 * a - 2 * k) / (3 * a)| ^ (P + 1) / k
      ≤ ((1 : ℚ) / 3) ^ (P + 1) / k := div_le_div_of_nonneg_right hp (le_of_lt hk)
    _ ≤ ((1 : ℚ) / 3) ^ (P + 1) / a :=
      div_le_div_of_nonneg_left (by positivity) ha hak
    _ = 1 / (a * 3 ^ (P + 1)) := by rw [div_pow, one_pow]; ring

def block (a m : ℕ) : Finset ℕ := Ico (min a (m + 1)) (min (2 * a) (m + 1))

theorem mem_block_bounds {a m k : ℕ} (hk : k ∈ block a m) : a ≤ k ∧ k < 2 * a := by
  simp only [block, mem_Ico] at hk
  omega

theorem card_block (a m : ℕ) : (block a m).card ≤ a := by
  simp only [block, Nat.card_Ico]
  omega

def blockApprox (a m P : ℕ) : ℚ := ∑ k ∈ block a m, term a k P
def blockExact (a m : ℕ) : ℚ := ∑ k ∈ block a m, 1 / (k : ℚ)
def harmonic (m : ℕ) : ℚ := ∑ k ∈ Ico 1 (m + 1), 1 / (k : ℚ)
def rawApprox (L m P : ℕ) : ℚ := ∑ b ∈ range L, blockApprox (2 ^ b) m P

theorem block_error {a m P : ℕ} (ha : 0 < a) :
    |blockApprox a m P - blockExact a m| ≤ 1 / (3 : ℚ) ^ (P + 1) := by
  unfold blockApprox blockExact
  rw [← sum_sub_distrib]
  calc
    |∑ k ∈ block a m, (term a k P - 1 / (k : ℚ))|
      ≤ ∑ k ∈ block a m, |term a k P - 1 / (k : ℚ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ block a m, 1 / ((a : ℚ) * 3 ^ (P + 1)) := by
      apply sum_le_sum
      intro k hk
      obtain ⟨hak, hka⟩ := mem_block_bounds hk
      exact term_error (by exact_mod_cast ha) (by exact_mod_cast hak)
        (by exact_mod_cast Nat.le_of_lt hka) P
    _ = (block a m).card / ((a : ℚ) * 3 ^ (P + 1)) := by
      simp [div_eq_mul_inv]
    _ ≤ (a : ℚ) / ((a : ℚ) * 3 ^ (P + 1)) := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast card_block a m
      · positivity
    _ = 1 / (3 : ℚ) ^ (P + 1) := by
      field_simp

theorem blocks_partition (L m : ℕ) :
    (∑ b ∈ range L, blockExact (2 ^ b) m) =
      ∑ k ∈ Ico 1 (min (2 ^ L) (m + 1)), 1 / (k : ℚ) := by
  induction L with
  | zero => simp [blockExact]
  | succ L ih =>
    rw [sum_range_succ, ih]
    unfold blockExact block
    rw [pow_succ]
    have hlow : 1 ≤ min (2 ^ L) (m + 1) := by
      apply le_min
      · exact Nat.one_le_pow L 2 (by decide)
      · omega
    have hhigh : min (2 ^ L) (m + 1) ≤ min (2 ^ L * 2) (m + 1) := by
      omega
    simpa [Nat.mul_comm] using sum_Ico_consecutive (fun k => 1 / (k : ℚ)) hlow hhigh

theorem raw_error {L m P : ℕ} (hm : m < 2 ^ L) :
    |rawApprox L m P - harmonic m| ≤ (L : ℚ) / 3 ^ (P + 1) := by
  have hp := blocks_partition L m
  rw [min_eq_right (by omega)] at hp
  unfold rawApprox harmonic
  rw [← hp, ← sum_sub_distrib]
  calc
    |∑ b ∈ range L, (blockApprox (2 ^ b) m P - blockExact (2 ^ b) m)|
      ≤ ∑ b ∈ range L, |blockApprox (2 ^ b) m P - blockExact (2 ^ b) m| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _b ∈ range L, 1 / (3 : ℚ) ^ (P + 1) := by
      apply sum_le_sum
      intro b _
      exact block_error (by positivity)
    _ = (L : ℚ) / 3 ^ (P + 1) := by simp [div_eq_mul_inv]

theorem cast_le_two_pow (L : ℕ) : (L : ℚ) ≤ 2 ^ L := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    have h1 : (1 : ℚ) ≤ 2 ^ L := one_le_pow₀ (by norm_num)
    push_cast
    rw [pow_succ]
    linarith

theorem scaled_budget {j L : ℕ} (hj : j < 2 ^ L) :
    (2 : ℚ) * (j : ℚ) ^ 2 * L / 3 ^ (4 * L + 5) < 1 / 16 := by
  have hjq : (j : ℚ) ≤ (2 : ℚ) ^ L := by exact_mod_cast Nat.le_of_lt hj
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ j) hjq 2
  have hL := cast_le_two_pow L
  have hnum : (2 : ℚ) * (j : ℚ) ^ 2 * L ≤ 2 * (8 : ℚ) ^ L := by
    calc
      (2 : ℚ) * (j : ℚ) ^ 2 * L ≤ 2 * ((2 : ℚ) ^ L) ^ 2 * L := by
        gcongr
      _ ≤ 2 * ((2 : ℚ) ^ L) ^ 2 * (2 : ℚ) ^ L := by gcongr
      _ = 2 * (8 : ℚ) ^ L := by
        rw [← pow_mul, Nat.mul_comm L 2, pow_mul, mul_assoc, ← mul_pow]
        norm_num
  have hp : (8 : ℚ) ^ L ≤ 81 ^ L := pow_le_pow_left₀ (by norm_num) (by norm_num) L
  have hden : (3 : ℚ) ^ (4 * L + 5) = 243 * 81 ^ L := by
    rw [pow_add, pow_mul]
    norm_num
    ring
  rw [hden]
  have hpos : (0 : ℚ) < 81 ^ L := by positivity
  apply (div_lt_iff₀ (by positivity : (0 : ℚ) < 243 * 81 ^ L)).2
  nlinarith

def harmonicApprox (L m : ℕ) : ℚ :=
  if m = 0 then 0 else if m = 1 then 1 else rawApprox L m (4 * L + 4)

theorem harmonic_zero : harmonic 0 = 0 := by simp [harmonic]
theorem harmonic_one : harmonic 1 = 1 := by norm_num [harmonic]

theorem harmonic_error {L m : ℕ} (hm : m < 2 ^ L) :
    |harmonicApprox L m - harmonic m| ≤ (L : ℚ) / 3 ^ (4 * L + 5) := by
  unfold harmonicApprox
  split_ifs with h0 h1
  · subst m
    rw [harmonic_zero]
    simp
    positivity
  · subst m
    rw [harmonic_one]
    simp
    positivity
  · simpa only [Nat.add_assoc] using (raw_error (P := 4 * L + 4) hm)

def ideal (j m : ℕ) : ℚ := 2 * (j : ℚ) ^ 2 * harmonic m - (m : ℚ) ^ 2
def approx (L j m : ℕ) : ℚ := 2 * (j : ℚ) ^ 2 * harmonicApprox L m - (m : ℚ) ^ 2
def quota (L j m : ℕ) : ℤ := ⌊approx L j m⌋

theorem approximation_certificate {L j m : ℕ} (hj : j < 2 ^ L) (hmj : m ≤ j) :
    |approx L j m - ideal j m| < 1 / 16 := by
  have hh := harmonic_error (lt_of_le_of_lt hmj hj)
  have hb := scaled_budget hj
  have heq : approx L j m - ideal j m =
      2 * (j : ℚ) ^ 2 * (harmonicApprox L m - harmonic m) := by
    unfold approx ideal
    ring
  rw [heq, abs_mul, abs_of_nonneg (by positivity : (0 : ℚ) ≤ 2 * (j : ℚ) ^ 2)]
  calc
    2 * (j : ℚ) ^ 2 * |harmonicApprox L m - harmonic m|
      ≤ 2 * (j : ℚ) ^ 2 * ((L : ℚ) / 3 ^ (4 * L + 5)) := by gcongr
    _ < 1 / 16 := by simpa only [mul_div_assoc] using hb

theorem quota_error {L j m : ℕ} (hj : j < 2 ^ L) (hmj : m ≤ j) :
    -(17 : ℚ) / 16 < (quota L j m : ℚ) - ideal j m ∧
      (quota L j m : ℚ) - ideal j m ≤ 1 / 16 := by
  have he := approximation_certificate hj hmj
  rw [abs_lt] at he
  have hf := Int.floor_le (approx L j m)
  have hg := Int.lt_floor_add_one (approx L j m)
  unfold quota
  constructor <;> linarith

theorem harmonic_succ (m : ℕ) : harmonic (m + 1) = harmonic m + 1 / (m + 1 : ℚ) := by
  unfold harmonic
  rw [sum_Ico_succ_top (by omega : 1 ≤ m + 1)]
  push_cast
  rfl

def rowIdeal (j m : ℕ) : ℚ := 2 * (j : ℚ) ^ 2 / m - 2 * m + 1
def rowQuota (L j m : ℕ) : ℤ := quota L j m - quota L j (m - 1)

theorem ideal_step {j m : ℕ} (hm : 0 < m) :
    ideal j m - ideal j (m - 1) = rowIdeal j m := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  simp only [ideal, harmonic_succ, rowIdeal]
  push_cast
  ring

theorem row_quota_error {L j m : ℕ} (hj : j < 2 ^ L) (hm : 0 < m) (hmj : m ≤ j) :
    -(9 : ℚ) / 8 < (rowQuota L j m : ℚ) - rowIdeal j m ∧
      (rowQuota L j m : ℚ) - rowIdeal j m < 9 / 8 := by
  have h0 := quota_error hj hmj
  have h1 := quota_error hj (show m - 1 ≤ j by omega)
  have hs := ideal_step (j := j) hm
  unfold rowQuota
  push_cast
  constructor <;> linarith

theorem quota_zero (L j : ℕ) : quota L j 0 = 0 := by
  simp [quota, approx, harmonicApprox]

theorem quota_one (L j : ℕ) : quota L j 1 = 2 * (j : ℤ) ^ 2 - 1 := by
  simp [quota, approx, harmonicApprox]
  norm_cast

theorem row_quota_nonnegative {L j m : ℕ} (hj : j < 2 ^ L)
    (hm : 0 < m) (hmj : m ≤ j) : 0 ≤ rowQuota L j m := by
  have he := row_quota_error hj hm hmj
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hmjQ : (m : ℚ) ≤ j := by exact_mod_cast hmj
  have hsq : (m : ℚ) ^ 2 ≤ (j : ℚ) ^ 2 := pow_le_pow_left₀ (le_of_lt hmQ) hmjQ 2
  have hideal : (1 : ℚ) ≤ rowIdeal j m := by
    have hdiv : 2 * (m : ℚ) ≤ 2 * (j : ℚ) ^ 2 / m :=
      (le_div_iff₀ hmQ).2 (by nlinarith)
    unfold rowIdeal
    linarith
  by_contra h
  have hneg : rowQuota L j m ≤ -1 := by omega
  have hnegQ : (rowQuota L j m : ℚ) ≤ -1 := by exact_mod_cast hneg
  linarith

theorem row_ideal_growth {j m : ℕ} (hm : 0 < m) (hmj : m ≤ j) :
    rowIdeal j m + 4 ≤ rowIdeal (j + 1) m := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hmjQ : (m : ℚ) ≤ j := by exact_mod_cast hmj
  have hi : rowIdeal (j + 1) m = rowIdeal j m + (4 * j + 2 : ℚ) / m := by
    unfold rowIdeal
    push_cast
    ring
  have hd : (4 : ℚ) ≤ (4 * j + 2 : ℚ) / m := (le_div_iff₀ hmQ).2 (by linarith)
  linarith

theorem row_quota_growth {L L' j m : ℕ} (hj : j < 2 ^ L) (hj' : j + 1 < 2 ^ L')
    (hm : 0 < m) (hmj : m ≤ j) : rowQuota L j m + 2 ≤ rowQuota L' (j + 1) m := by
  have he := row_quota_error hj hm hmj
  have he' := row_quota_error hj' hm (show m ≤ j + 1 by omega)
  have hg := row_ideal_growth hm hmj
  by_contra h
  have hf : rowQuota L' (j + 1) m ≤ rowQuota L j m + 1 := by omega
  have hfQ : (rowQuota L' (j + 1) m : ℚ) ≤ (rowQuota L j m : ℚ) + 1 := by
    exact_mod_cast hf
  linarith

def actualRow (j m : ℕ) : ℤ := 2 * ⌊(j : ℚ) ^ 2 / m⌋ - 2 * m + 1

theorem actual_row_le_ideal (j m : ℕ) : (actualRow j m : ℚ) ≤ rowIdeal j m := by
  have hf := Int.floor_le ((j : ℚ) ^ 2 / m)
  unfold actualRow rowIdeal
  push_cast
  simp only [mul_div_assoc]
  linarith

theorem next_row_covers {L' j m : ℕ} (hj' : j + 1 < 2 ^ L')
    (hm : 0 < m) (hmj : m ≤ j) : actualRow j m ≤ rowQuota L' (j + 1) m := by
  have he' := row_quota_error hj' hm (show m ≤ j + 1 by omega)
  have hg := row_ideal_growth hm hmj
  have ha := actual_row_le_ideal j m
  have hq : (actualRow j m : ℚ) ≤ rowQuota L' (j + 1) m := by linarith
  exact_mod_cast hq

end SquareStagePairing.Harmonic
