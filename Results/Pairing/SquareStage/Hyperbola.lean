module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Prod
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# A harmonic lower bound for a discrete product region

- **Claim:** the number of nonnegative pairs with `(x + 1) * (y + 1) ≤ a`
  is at least `2 * j^2 * harmonic j - j^2 - 2 * j` whenever `j^2 ≤ a`.
- **Main declaration:** `SquareStagePairing.Hyperbola.region_harmonic_lower`.
- **Not proved:** a matching upper estimate, the divisor problem's sharp
  error term, or an algorithmic running-time bound.
- **Author:** avocardio (human), with OpenAI Codex (GPT family).

This is the elementary Dirichlet hyperbola argument, using the union of
two transposed rectangles and the bound `floor t > t - 1`.
No novelty is asserted for that counting argument.
-/

@[expose] public section

namespace SquareStagePairing.Hyperbola
open Finset
open scoped BigOperators

def product (p : ℕ × ℕ) : ℕ := (p.1+1)*(p.2+1)
def region (a : ℕ) : Finset (ℕ × ℕ) :=
  ((range a) ×ˢ (range a)).filter (fun p => product p ≤ a)
def rectangle (a j : ℕ) : Finset (ℕ × ℕ) :=
  (range j).biUnion (fun u => (range (a/(u+1))).image (fun v => (u,v)))

theorem mem_region (a : ℕ) (p : ℕ × ℕ) : p ∈ region a ↔ product p ≤ a := by
  simp only [region, mem_filter, mem_product, mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hx : p.1+1 ≤ product p := by unfold product; nlinarith
    have hy : p.2+1 ≤ product p := by unfold product; nlinarith
    exact ⟨⟨by omega, by omega⟩,h⟩

theorem mem_rectangle (a j : ℕ) (p : ℕ × ℕ) :
    p ∈ rectangle a j ↔ p.1 < j ∧ product p ≤ a := by
  rcases p with ⟨u,v⟩
  simp only [rectangle, mem_biUnion, mem_range, mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨x,hx,y,hy,hxu,hyv⟩
    subst x; subst y
    refine ⟨hx,?_⟩
    have hh := (Nat.le_div_iff_mul_le (by omega : 0 < u+1)).1 (show v+1 ≤ a/(u+1) by omega)
    simpa [product, Nat.mul_comm] using hh
  · rintro ⟨hu,hp⟩
    refine ⟨u,hu,v,?_,rfl,rfl⟩
    have hh : (v+1)*(u+1) ≤ a := by simpa [product, Nat.mul_comm] using hp
    have := (Nat.le_div_iff_mul_le (by omega : 0 < u+1)).2 hh
    omega

theorem rectangle_card (a j : ℕ) :
    (rectangle a j).card = ∑ u ∈ range j, a/(u+1) := by
  unfold rectangle
  rw [card_biUnion]
  · apply sum_congr rfl
    intro u _
    rw [card_image_of_injective _ (by intro x y h; exact Prod.mk.inj h |>.2), card_range]
  · intro x _hx y _hy hxy
    apply disjoint_left.2
    intro p hp hq
    rcases mem_image.1 hp with ⟨v,_hv,hv'⟩
    rcases mem_image.1 hq with ⟨w,_hw,hw'⟩
    exact hxy (by simpa using congrArg Prod.fst (hv'.trans hw'.symm))

theorem rectangle_swap_inter (a j : ℕ) (hj : j*j ≤ a) :
    rectangle a j ∩ (rectangle a j).image Prod.swap = (range j) ×ˢ (range j) := by
  ext p
  have hs : p ∈ (rectangle a j).image Prod.swap ↔ p.2 < j ∧ product p ≤ a := by
    simp only [mem_image]
    constructor
    · rintro ⟨q,hq,hqp⟩
      subst p
      simpa only [Prod.fst_swap, Prod.snd_swap, product, Nat.mul_comm] using
        (mem_rectangle a j q).1 hq
    · intro h
      refine ⟨p.swap,?_,by simp⟩
      apply (mem_rectangle a j p.swap).2
      simpa only [Prod.fst_swap, Prod.snd_swap, product, Nat.mul_comm] using h
  rw [mem_inter, mem_rectangle, hs, mem_product]
  simp only [mem_range]
  constructor
  · exact fun h => ⟨h.1.1,h.2.1⟩
  · intro h
    have hp : product p ≤ a := by
      have := Nat.mul_le_mul (show p.1+1 ≤ j by omega) (show p.2+1 ≤ j by omega)
      exact this.trans hj
    exact ⟨⟨h.1,hp⟩,⟨h.2,hp⟩⟩

theorem hyperbola_lower (a j : ℕ) (hj : j*j ≤ a) :
    2*(∑ u ∈ range j, a/(u+1)) ≤ (region a).card + j*j := by
  have hu : rectangle a j ∪ (rectangle a j).image Prod.swap ⊆ region a := by
    intro p hp
    apply (mem_region a p).2
    rcases mem_union.1 hp with h|h
    · exact ((mem_rectangle a j p).1 h).2
    · rcases mem_image.1 h with ⟨q,hq,hqp⟩
      subst p
      simpa only [product, Prod.fst_swap, Prod.snd_swap, Nat.mul_comm] using
        ((mem_rectangle a j q).1 hq).2
  have hc := card_union_add_card_inter (rectangle a j) ((rectangle a j).image Prod.swap)
  rw [rectangle_swap_inter a j hj, card_product, card_range,
    card_image_of_injective _ Prod.swap_injective, rectangle_card] at hc
  have hle := card_le_card hu
  omega

theorem harmonic_floor_lower (a j : ℕ) (hj : j*j ≤ a) :
    (j:ℝ)^2*(harmonic j:ℝ)-j ≤ ((∑ u ∈ range j, a/(u+1):ℕ):ℝ) := by
  have hterm (u : ℕ) : (j:ℝ)^2/(u+1)-1 ≤ ((a/(u+1):ℕ):ℝ) := by
    have hp : (0:ℝ) < (u:ℝ)+1 := by positivity
    have hn := Nat.lt_mul_div_succ a (by omega : 0 < u+1)
    have hn' : (a:ℝ) < ((u:ℝ)+1)*(((a/(u+1):ℕ):ℝ)+1) := by exact_mod_cast hn
    have hj' : (j:ℝ)^2 ≤ a := by rw [pow_two]; exact_mod_cast hj
    have hd : (j:ℝ)^2/(u+1) ≤ ((a/(u+1):ℕ):ℝ)+1 :=
      (div_le_iff₀ hp).2 (by nlinarith)
    linarith
  have hs := sum_le_sum (s := range j) (fun u _ => hterm u)
  have heq : (∑ u ∈ range j, ((j:ℝ)^2/(u+1)-1)) = (j:ℝ)^2*(harmonic j:ℝ)-j := by
    simp only [sum_sub_distrib, div_eq_mul_inv, ← mul_sum, sum_const,
      card_range, nsmul_eq_mul, mul_one, harmonic, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast, Rat.cast_add, Rat.cast_one, Nat.cast_add, Nat.cast_one]
  rw [heq] at hs
  simpa only [Nat.cast_sum] using hs

theorem region_harmonic_lower (a j : ℕ) (hj : j*j ≤ a) :
    2*(j:ℝ)^2*(harmonic j:ℝ)-(j:ℝ)^2-2*j ≤ ((region a).card:ℝ) := by
  have hc := hyperbola_lower a j hj
  have hc' : 2*((∑ u ∈ range j, a/(u+1):ℕ):ℝ) ≤ ((region a).card:ℝ)+(j:ℝ)^2 := by
    rw [pow_two]
    exact_mod_cast hc
  have hh := harmonic_floor_lower a j hj
  linarith

end SquareStagePairing.Hyperbola
