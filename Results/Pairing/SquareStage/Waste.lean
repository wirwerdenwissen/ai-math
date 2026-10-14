module

public import Results.Pairing.SquareStage.Hyperbola
public import Results.Pairing.SquareStage.ArithmeticCounting
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt

/-!
# Finite harmonic bounds for square-stage waste

- **Claim:** the stated span coverage bound implies explicit finite and
  `O(√A log A)` excess-span bounds over the actual divisor-region cardinality.
- **Main declaration:** `SquareStagePairing.Waste.waste_bigO`,
  `SquareStagePairing.Waste.waste_finite`.
- **Not proved:** construction of a pairing satisfying the coverage hypothesis;
  `Results.Pairing.SquareStage.Final` discharges it for the concrete pairing.
- **Author:** avocardio (human); OpenAI Codex (GPT family).

These estimates use finite hyperbola counts and standard harmonic/logarithmic
inequalities from Mathlib, without any divisor-problem error estimate.
-/

@[expose] public section

namespace SquareStagePairing.Waste
open Finset
open scoped BigOperators

def ideal (j m : ℕ) : ℝ := 2 * (j : ℝ)^2 * (harmonic m : ℝ) - (m : ℝ)^2

theorem ideal_row (j m : ℕ) :
    ideal j (m+1) - ideal j m = 2 * (j:ℝ)^2 / (m+1) - 2*m - 1 := by
  simp only [ideal, harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast,
    Nat.cast_add, Nat.cast_one]
  ring

theorem new_rows_bound (j : ℕ) :
    ideal (j+2) (j+2) - ideal (j+2) j ≤ 8 := by
  have h₁ := ideal_row (j+2) j
  have h₂ := ideal_row (j+2) (j+1)
  have hpos : (0:ℝ) < j+1 := by positivity
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at h₁ h₂
  have heq₁ : 2 * ((j:ℝ)+2)^2 / (j+1) - 2*j - 1 = 5 + 2/(j+1) := by
    field_simp
    ring
  have heq₂ : 2 * ((j:ℝ)+2)^2 / ((j+1)+1) - 2*(j+1) - 1 = 1 := by
    field_simp
    ring
  have hfrac : (2:ℝ)/(j+1) ≤ 2 := (div_le_iff₀ hpos).2 (by nlinarith [Nat.cast_nonneg (α := ℝ) j])
  rw [heq₁] at h₁
  rw [heq₂] at h₂
  have hj : j+1+1 = j+2 := by omega
  rw [hj] at h₂
  linarith

theorem ideal_two_stage_gap (j : ℕ) :
    ideal (j+2) (j+2) - ideal j j ≤
      (8*(j:ℝ)+8)*(harmonic j:ℝ)+8 := by
  have h := new_rows_bound j
  have heq : ideal (j+2) j - ideal j j = (8*(j:ℝ)+8)*(harmonic j:ℝ) := by
    simp only [ideal, Nat.cast_add, Nat.cast_ofNat]
    ring
  linarith

/-- Direct finite estimate; no divisor-error asymptotic is assumed. -/
theorem waste_finite (j W D : ℕ)
    (hW : (W:ℝ) ≤ ideal (j+2) (j+2)+1)
    (hD : ideal j j - 2*j ≤ (D:ℝ)) (hDW : D ≤ W) :
    ((W-D:ℕ):ℝ) ≤ (8*(j:ℝ)+8)*(harmonic j:ℝ)+2*j+9 := by
  rw [Nat.cast_sub hDW]
  have hgap := ideal_two_stage_gap j
  linarith

theorem waste_log_bound (j W D : ℕ) (hj : 1 ≤ j)
    (hW : (W:ℝ) ≤ ideal (j+2) (j+2)+1)
    (hD : ideal j j - 2*j ≤ (D:ℝ)) (hDW : D ≤ W) :
    ((W-D:ℕ):ℝ) ≤ 19*((j:ℝ)+1)*(1+Real.log j) := by
  have hf := waste_finite j W D hW hD hDW
  have hh := harmonic_le_one_add_log j
  have hj' : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hl : 0 ≤ Real.log (j:ℝ) := Real.log_nonneg hj'
  have hm : (8*(j:ℝ)+8)*(harmonic j:ℝ) ≤
      (8*(j:ℝ)+8)*(1+Real.log j) := mul_le_mul_of_nonneg_left hh (by positivity)
  nlinarith

theorem divisor_harmonic_lower (a j : ℕ) (hj : j*j ≤ a) :
    ideal j j - 2*j ≤ (SquareStagePairing.ArithmeticCounting.divisorCount a:ℝ) :=
  SquareStagePairing.Hyperbola.region_harmonic_lower a j hj

theorem sqrt_waste_bound (a W : ℕ) (ha : 1 ≤ a) (hlog : 1 ≤ Real.log (a:ℝ))
    (hW : (W:ℝ) ≤ ideal (Nat.sqrt a+2) (Nat.sqrt a+2)+1)
    (hDW : SquareStagePairing.ArithmeticCounting.divisorCount a ≤ W) :
    ((W-SquareStagePairing.ArithmeticCounting.divisorCount a:ℕ):ℝ) ≤
      76*Real.sqrt a*Real.log a := by
  have hj : 1 ≤ Nat.sqrt a := (Nat.le_sqrt).2 (by simpa using ha)
  have hd := divisor_harmonic_lower a (Nat.sqrt a) (Nat.sqrt_le a)
  have hb := waste_log_bound (Nat.sqrt a) W (SquareStagePairing.ArithmeticCounting.divisorCount a) hj hW hd hDW
  have hja : (Nat.sqrt a:ℝ) ≤ a := by exact_mod_cast Nat.sqrt_le_self a
  have hjpos : (0:ℝ) < Nat.sqrt a := by exact_mod_cast (show 0 < Nat.sqrt a by omega)
  have hl := Real.log_le_log hjpos hja
  have hjs : (Nat.sqrt a:ℝ) ≤ Real.sqrt a := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.sqrt_le' a
  have has : (1:ℝ) ≤ Real.sqrt a := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    exact_mod_cast ha
  have hf : 0 ≤ 1+Real.log (Nat.sqrt a:ℝ) := by
    have hjone : (1:ℝ) ≤ Nat.sqrt a := by exact_mod_cast hj
    have := Real.log_nonneg hjone
    linarith
  have hm := mul_le_mul (show (Nat.sqrt a:ℝ)+1 ≤ 2*Real.sqrt a by linarith)
    (show 1+Real.log (Nat.sqrt a:ℝ) ≤ 2*Real.log a by linarith)
    hf (by positivity : (0:ℝ) ≤ 2*Real.sqrt a)
  nlinarith

/-- The full asymptotic estimate, conditional only on the displayed actual
    span coverage bound. The concrete square-stage instance discharges it. -/
theorem waste_bigO (W : ℕ → ℕ)
    (hW : ∀ a, 1 ≤ a → (W a:ℝ) ≤ ideal (Nat.sqrt a+2) (Nat.sqrt a+2)+1)
    (hDW : ∀ a, SquareStagePairing.ArithmeticCounting.divisorCount a ≤ W a) :
    (fun a => ((W a-SquareStagePairing.ArithmeticCounting.divisorCount a:ℕ):ℝ))
      =O[Filter.atTop] (fun a => Real.sqrt a*Real.log a) := by
  apply Asymptotics.IsBigO.of_bound 76
  have ht : Filter.Tendsto (fun a : ℕ => Real.log (a:ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [Filter.eventually_ge_atTop 1, ht.eventually (Filter.eventually_ge_atTop 1)]
    with a ha hl
  have hb := sqrt_waste_bound a (W a) ha hl (hW a ha) (hDW a)
  have hp : 0 ≤ Real.sqrt a*Real.log a := mul_nonneg (Real.sqrt_nonneg _) (by linarith)
  have hn : (0:ℝ) ≤ ((W a-SquareStagePairing.ArithmeticCounting.divisorCount a:ℕ):ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn, abs_of_nonneg hp,
    mul_assoc] using hb

end SquareStagePairing.Waste
