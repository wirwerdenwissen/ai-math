module

public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Ring.RingNF
public import Results.Pairing.SquareStage.Counting
public import Results.Pairing.SquareStage.Hyperbola

/-!
# Product regions, enumeration spans, and conditional counting reductions

- **Claim:** the product-region cardinality equals the divisor sum; its span
  bounds its cardinality; the stated waste or localization certificates justify
  exact-span or exact-count recovery and the displayed conditional cost bounds.
- **Main declaration:** `SquareStagePairing.ArithmeticCounting.divisorCount_eq_floor_sum`,
  `SquareStagePairing.ArithmeticCounting.divisorCount_le_span`,
  `SquareStagePairing.ArithmeticCounting.exact_arithmetic_count`.
- **Not proved:** two-sided localization for the concrete square pairing,
  unconditional decoder-time bounds, or correspondence of the abstract charges
  with machine execution. Computing a supplied localization budget is external.
- **Author:** avocardio (human); OpenAI Codex (GPT family).

Coordinates `(x, y)` represent `(x + 1, y + 1)`. Exact span recovery needs
one-sided waste control; exact cardinality recovery additionally assumes the
two-sided `Localized` property. The latter is not inferred from waste alone.
The square pairing's final waste theorem uses the region/cardinality/span
bridge, without instantiating the stronger computational reductions here.
-/

@[expose] public section

namespace SquareStagePairing.ArithmeticCounting

def product (p : Nat × Nat) : Nat := (p.1+1)*(p.2+1)

def region (a : Nat) : Finset (Nat × Nat) :=
  (Finset.range a ×ˢ Finset.range a).filter (fun p => product p ≤ a)

def divisorCount (a : Nat) : Nat := (region a).card

theorem mem_region (a : Nat) (p : Nat × Nat) :
    p ∈ region a ↔ product p ≤ a := by
  simp only [region, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro h
    have hu : p.1+1 ≤ product p := by unfold product; nlinarith [Nat.zero_le (p.1*p.2)]
    have hv : p.2+1 ≤ product p := by unfold product; nlinarith [Nat.zero_le (p.1*p.2)]
    exact ⟨⟨by omega, by omega⟩, h⟩

theorem divisorCount_eq_floor_sum (a : Nat) :
    divisorCount a = ∑ u ∈ Finset.range a, a/(u+1) := by
  have he : region a = SquareStagePairing.Hyperbola.rectangle a a := by
    ext p
    rw [mem_region, SquareStagePairing.Hyperbola.mem_rectangle]
    change product p ≤ a ↔ p.1 < a ∧ product p ≤ a
    constructor
    · intro hp
      have hu : p.1+1 ≤ product p := by unfold product; nlinarith
      exact ⟨by omega, hp⟩
    · exact fun hp => hp.2
  unfold divisorCount
  rw [he, SquareStagePairing.Hyperbola.rectangle_card]

def inside (g : Equiv Nat (Nat × Nat)) (a i : Nat) : Bool :=
  decide (product (g i) ≤ a)

def span (g : Equiv Nat (Nat × Nat)) (a : Nat) : Nat :=
  (region a).sup (fun p => g.symm p+1)

theorem rank_lt_span (g : Equiv Nat (Nat × Nat)) (a : Nat) (p : Nat × Nat)
    (hp : p ∈ region a) : g.symm p < span g a := by
  have h : g.symm p+1 ≤ (region a).sup (fun q => g.symm q+1) :=
    Finset.le_sup (f := fun q => g.symm q+1) hp
  exact h

theorem count_eq_card (p : Nat → Bool) (n : Nat) :
    SquareStagePairing.Counting.count p n = ((Finset.range n).filter (fun i => p i = true)).card := by
  induction n with
  | zero => simp [SquareStagePairing.Counting.count]
  | succ n ih =>
    by_cases hp : p n = true
    · simp [SquareStagePairing.Counting.count, Finset.range_add_one, Finset.filter_insert, hp, ih]
    · simp [SquareStagePairing.Counting.count, Finset.range_add_one, Finset.filter_insert, hp, ih]

theorem prefix_eq_image (g : Equiv Nat (Nat × Nat)) (a : Nat) :
    ((Finset.range (span g a)).filter (fun i => inside g a i = true)) =
      (region a).image g.symm := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨_, hi⟩
    refine ⟨g i, ?_, by simp⟩
    apply (mem_region a (g i)).mpr
    simpa only [inside, decide_eq_true_eq] using hi
  · rintro ⟨p, hp, rfl⟩
    refine ⟨rank_lt_span g a p hp, ?_⟩
    have ht := (mem_region a p).mp hp
    simpa only [inside, Equiv.apply_symm_apply, decide_eq_true_eq] using ht

theorem count_at_span (g : Equiv Nat (Nat × Nat)) (a : Nat) :
    SquareStagePairing.Counting.count (inside g a) (span g a) = divisorCount a := by
  rw [count_eq_card, prefix_eq_image]
  exact Finset.card_image_of_injective (region a) g.symm.injective

theorem span_positive (g : Equiv Nat (Nat × Nat)) (a : Nat) (ha : 0 < a) :
    0 < span g a := by
  have hp : (0,0) ∈ region a := by
    apply (mem_region a _).mpr
    simpa [product] using Nat.succ_le_of_lt ha
  have hr := rank_lt_span g a (0,0) hp
  omega

theorem span_finished (g : Equiv Nat (Nat × Nat)) (a i : Nat)
    (hi : span g a ≤ i) : inside g a i = false := by
  by_cases hp : product (g i) ≤ a
  · have hr := rank_lt_span g a (g i) ((mem_region a _).mpr hp)
    simp only [Equiv.symm_apply_apply] at hr
    omega
  · simp [inside, hp]

theorem span_last (g : Equiv Nat (Nat × Nat)) (a : Nat) (ha : 0 < a) :
    inside g a (span g a-1) = true := by
  by_cases hlast : inside g a (span g a-1) = true
  · exact hlast
  · have hbound : span g a ≤ span g a-1 := by
      apply Finset.sup_le
      intro p hp
      have hr := rank_lt_span g a p hp
      have hne : g.symm p ≠ span g a-1 := by
        intro he
        have ht : inside g a (g.symm p) = true := by
          simpa only [inside, Equiv.apply_symm_apply, decide_eq_true_eq] using
            (mem_region a p).mp hp
        rw [he] at ht
        exact hlast ht
      omega
    have hpos := span_positive g a ha
    omega

theorem divisorCount_le_span (g : Equiv Nat (Nat × Nat)) (a : Nat) :
    divisorCount a ≤ span g a := by
  have hc := SquareStagePairing.Counting.count_complement (inside g a) (span g a)
  rw [count_at_span] at hc
  omega

theorem certificate (g : Equiv Nat (Nat × Nat)) (a k : Nat)
    (ha : 0 < a) (hwaste : span g a-divisorCount a ≤ k) :
    SquareStagePairing.Counting.SpanCertificate (inside g a) (span g a) k := by
  refine ⟨span_positive g a ha, span_last g a ha, span_finished g a, ?_⟩
  have hc := SquareStagePairing.Counting.count_complement (inside g a) (span g a)
  rw [count_at_span] at hc
  omega

theorem divisorCount_le_square (a : Nat) : divisorCount a ≤ a*a := by
  have h := Finset.card_filter_le (Finset.range a ×ˢ Finset.range a)
    (fun p => product p ≤ a)
  simpa only [divisorCount, region, Finset.card_product, Finset.card_range] using h

theorem span_le_square_add (g : Equiv Nat (Nat × Nat)) (a k : Nat)
    (hwaste : span g a-divisorCount a ≤ k) : span g a ≤ a*a+k := by
  have hl := divisorCount_le_span g a
  have hu := divisorCount_le_square a
  omega

/-- Literal set containment for both sides of the cutoff; no smoothness or
    displacement inference is silently substituted for the early inclusion. -/
def Localized (g : Equiv Nat (Nat × Nat)) (a k : Nat) : Prop :=
  (∀ i, i < divisorCount a-k → g i ∈ region a) ∧
  (∀ p, p ∈ region a → g.symm p < divisorCount a+k)

theorem localized_waste (g : Equiv Nat (Nat × Nat)) (a k : Nat)
    (hloc : Localized g a k) : span g a-divisorCount a ≤ k := by
  have hs : span g a ≤ divisorCount a+k := by
    apply Finset.sup_le
    intro p hp
    exact hloc.2 p hp
  omega

theorem exact_arithmetic_count (g : Equiv Nat (Nat × Nat)) (a k : Nat)
    (ha : 0 < a) (hloc : Localized g a k) :
    SquareStagePairing.Counting.localizedCount (inside g a) k (a*a+k) = divisorCount a := by
  have hw := localized_waste g a k hloc
  apply SquareStagePairing.Counting.localizedCount_correct (inside g a) (divisorCount a) (span g a)
    k (a*a+k) (certificate g a k ha hw) (span_le_square_add g a k hw)
    (count_at_span g a)
  intro i hi
  have hp := (mem_region a (g i)).mp (hloc.1 i hi)
  simpa only [inside, decide_eq_true_eq] using hp

theorem exact_arithmetic_span (g : Equiv Nat (Nat × Nat)) (a k : Nat)
    (ha : 0 < a) (hwaste : span g a-divisorCount a ≤ k) :
    (SquareStagePairing.Counting.exactSpan (inside g a) k (a*a+k)).value = span g a :=
  SquareStagePairing.Counting.exactSpan_correct _ _ _ _ (certificate g a k ha hwaste)
    (span_le_square_add g a k hwaste)

theorem arithmetic_count_query_bound (g : Equiv Nat (Nat × Nat)) (a k : Nat) :
    SquareStagePairing.Counting.localizedQueries (inside g a) k (a*a+k) ≤
      SquareStagePairing.Counting.bitlength (a*a+k)*(k+1)+2*k :=
  SquareStagePairing.Counting.localizedQueries_bound _ _ _

theorem arithmetic_count_binary_cost (g : Equiv Nat (Nat × Nat))
    (decoderTime coordinateBits : Nat → Nat) (a k b arith t l c : Nat)
    (ha : 0 < a) (hloc : Localized g a k)
    (ht : ∀ i, i ≤ (a*a+k)+k → decoderTime i ≤ t)
    (hl : ∀ i, i ≤ (a*a+k)+k → coordinateBits i ≤ l) :
    SquareStagePairing.Counting.localizedCost (inside g a)
        (SquareStagePairing.Counting.membershipBitCharge decoderTime coordinateBits b arith) c k (a*a+k) ≤
      SquareStagePairing.Counting.bitlength (a*a+k)*((k+1)*(t+arith*(l+b+1)^2)+c)+c+
        (2*k)*(t+arith*(l+b+1)^2)+4*c := by
  have hw := localized_waste g a k hloc
  exact SquareStagePairing.Counting.localized_binary_cost _ _ _ (span g a) k (a*a+k) b arith t l c
    (certificate g a k ha hw) (span_le_square_add g a k hw) ht hl

theorem arithmetic_query_bitlength (a k b i : Nat)
    (hi : i ≤ (a*a+k)+k) (hb : (a*a+k)+k < 2^b) :
    SquareStagePairing.Counting.bitlength i ≤ b :=
  SquareStagePairing.Counting.bitlength_le i b (by omega)

theorem polynomial_waste_rank_bits (a k d i : Nat)
    (hk : k ≤ a^d) (hi : i ≤ (a*a+k)+k) :
    SquareStagePairing.Counting.bitlength i ≤ (d+2)*SquareStagePairing.Counting.bitlength a+2 := by
  let b := SquareStagePairing.Counting.bitlength a
  have hb : a ≤ 2^b := Nat.le_of_lt (SquareStagePairing.Counting.lt_pow_bitlength a)
  have hs : a*a ≤ 2^(2*b) := by
    have hm := Nat.mul_le_mul hb hb
    simpa [Nat.pow_add, two_mul] using hm
  have hd : a^d ≤ 2^(d*b) := by
    have hm := Nat.pow_le_pow_left hb d
    simpa [← Nat.pow_mul, Nat.mul_comm] using hm
  have h2 : 2^(2*b) ≤ 2^((d+2)*b) :=
    Nat.pow_le_pow_right (by decide) (by nlinarith)
  have h3 : 2^(d*b) ≤ 2^((d+2)*b) :=
    Nat.pow_le_pow_right (by decide) (by nlinarith)
  have hpos : 0 < 2^((d+2)*b) := Nat.two_pow_pos _
  apply SquareStagePairing.Counting.bitlength_le
  have hp : 2^((d+2)*b+2) = 4*2^((d+2)*b) := by
    rw [Nat.pow_add]; norm_num; omega
  change i < 2^((d+2)*b+2)
  rw [hp]
  omega

/-- Here coordinateBits is the actual maximum binary output-coordinate length.
    The decoded coordinates need not be small merely because their input rank
    is small; the supplied output bound is a separate computational hypothesis. -/
def decoderCoordinateBits (g : Equiv Nat (Nat × Nat)) (i : Nat) : Nat :=
  max (SquareStagePairing.Counting.bitlength ((g i).1+1)) (SquareStagePairing.Counting.bitlength ((g i).2+1))

theorem arithmetic_actual_decoder_cost (g : Equiv Nat (Nat × Nat))
    (decoderTime : Nat → Nat) (a k b arith t l c : Nat)
    (ha : 0 < a) (hloc : Localized g a k)
    (ht : ∀ i, i ≤ (a*a+k)+k → decoderTime i ≤ t)
    (hl : ∀ i, i ≤ (a*a+k)+k → decoderCoordinateBits g i ≤ l) :
    SquareStagePairing.Counting.localizedCost (inside g a)
        (SquareStagePairing.Counting.membershipBitCharge decoderTime (decoderCoordinateBits g) b arith)
        c k (a*a+k) ≤
      SquareStagePairing.Counting.bitlength (a*a+k)*((k+1)*(t+arith*(l+b+1)^2)+c)+c+
        (2*k)*(t+arith*(l+b+1)^2)+4*c :=
  arithmetic_count_binary_cost g decoderTime (decoderCoordinateBits g) a k b arith t l c
    ha hloc ht hl

theorem cost_polynomial_envelope (fuel k b arith t l c p : Nat)
    (hf : fuel ≤ p) (hb : b ≤ p) (ha : arith ≤ p)
    (ht : t ≤ p) (hl : l ≤ p) (hc : c ≤ p) :
    fuel*((k+1)*(t+arith*(l+b+1)^2)+c)+c+
        (2*k)*(t+arith*(l+b+1)^2)+4*c ≤ 64*(k+1)*(p+1)^4 := by
  calc
    _ ≤ p*((k+1)*(p+p*(p+p+1)^2)+p)+p+(2*k)*(p+p*(p+p+1)^2)+4*p := by
      gcongr
    _ ≤ _ := by
      have h1 := Nat.zero_le (p*k)
      have h2 := Nat.zero_le (p^2*k)
      have h3 := Nat.zero_le (p^3*k)
      have h4 := Nat.zero_le (p^4*k)
      ring_nf
      omega

/-- Choosing p to be any fixed polynomial in input bit length gives
    (k+1) times a fixed polynomial in that length. The theorem uses the actual
    output-coordinate bit lengths and charges all listed arithmetic. -/
theorem arithmetic_uniform_polynomial_cost (g : Equiv Nat (Nat × Nat))
    (decoderTime : Nat → Nat) (a k b arith c p : Nat)
    (ha : 0 < a) (hloc : Localized g a k)
    (hb : b ≤ p) (harith : arith ≤ p) (hc : c ≤ p)
    (hf : SquareStagePairing.Counting.bitlength (a*a+k) ≤ p)
    (ht : ∀ i, i ≤ (a*a+k)+k → decoderTime i ≤ p)
    (hl : ∀ i, i ≤ (a*a+k)+k → decoderCoordinateBits g i ≤ p) :
    SquareStagePairing.Counting.localizedCost (inside g a)
        (SquareStagePairing.Counting.membershipBitCharge decoderTime (decoderCoordinateBits g) b arith)
        c k (a*a+k) ≤ 64*(k+1)*(p+1)^4 := by
  exact (arithmetic_actual_decoder_cost g decoderTime a k b arith p p c ha hloc ht hl).trans
    (cost_polynomial_envelope _ k b arith p p c p hf hb harith (by rfl) (by rfl) hc)

/-- Setup covers construction of A²+K and binary-length fuel. Computing the
    supplied bound K itself is external and must be charged separately. -/
def arithmeticTotalCost (g : Equiv Nat (Nat × Nat)) (decoderTime : Nat → Nat)
    (a k b arith c : Nat) : Nat :=
  SquareStagePairing.Counting.localizedCost (inside g a)
      (SquareStagePairing.Counting.membershipBitCharge decoderTime (decoderCoordinateBits g) b arith)
      c k (a*a+k) + arith*(b+1)^2

theorem arithmetic_total_polynomial_cost (g : Equiv Nat (Nat × Nat))
    (decoderTime : Nat → Nat) (a k b arith c p : Nat)
    (ha : 0 < a) (hloc : Localized g a k)
    (hb : b ≤ p) (harith : arith ≤ p) (hc : c ≤ p)
    (hf : SquareStagePairing.Counting.bitlength (a*a+k) ≤ p)
    (ht : ∀ i, i ≤ (a*a+k)+k → decoderTime i ≤ p)
    (hl : ∀ i, i ≤ (a*a+k)+k → decoderCoordinateBits g i ≤ p) :
    arithmeticTotalCost g decoderTime a k b arith c ≤ 65*(k+1)*(p+1)^4 := by
  have hrun := arithmetic_uniform_polynomial_cost g decoderTime a k b arith c p
    ha hloc hb harith hc hf ht hl
  have hsetup : arith*(b+1)^2 ≤ (k+1)*(p+1)^4 := by
    calc
      _ ≤ p*(p+1)^2 := by gcongr
      _ ≤ _ := by
        have h1 := Nat.zero_le (p*k)
        have h2 := Nat.zero_le (p^2*k)
        have h3 := Nat.zero_le (p^3*k)
        have h4 := Nat.zero_le (p^4*k)
        ring_nf
        omega
  unfold arithmeticTotalCost
  nlinarith

def rankBitBudget (a d : Nat) : Nat := (d+2)*SquareStagePairing.Counting.bitlength a+2

/-- End-to-end package with a certified bit budget, not an arbitrary bit-charge
    parameter. K is supplied; its computation is outside this reduction. -/
theorem arithmetic_polynomial_waste_reduction (g : Equiv Nat (Nat × Nat))
    (decoderTime : Nat → Nat) (a k d arith c p : Nat)
    (ha : 0 < a) (hloc : Localized g a k) (hk : k ≤ a^d)
    (hb : rankBitBudget a d ≤ p) (harith : arith ≤ p) (hc : c ≤ p)
    (ht : ∀ i, i ≤ (a*a+k)+k → decoderTime i ≤ p)
    (hl : ∀ i, i ≤ (a*a+k)+k → decoderCoordinateBits g i ≤ p) :
    SquareStagePairing.Counting.localizedCount (inside g a) k (a*a+k) = divisorCount a ∧
    (SquareStagePairing.Counting.bitlength a ≤ rankBitBudget a d ∧
      ∀ i, i ≤ (a*a+k)+k → SquareStagePairing.Counting.bitlength i ≤ rankBitBudget a d) ∧
    arithmeticTotalCost g decoderTime a k (rankBitBudget a d) arith c ≤
      65*(k+1)*(p+1)^4 := by
  refine ⟨exact_arithmetic_count g a k ha hloc, ⟨?_, ?_⟩, ?_⟩
  · unfold rankBitBudget
    nlinarith
  · intro i hi
    exact polynomial_waste_rank_bits a k d i hk hi
  · apply arithmetic_total_polynomial_cost g decoderTime a k (rankBitBudget a d)
      arith c p ha hloc hb harith hc
    · exact (polynomial_waste_rank_bits a k d (a*a+k) hk (by omega)).trans hb
    · exact ht
    · exact hl

end SquareStagePairing.ArithmeticCounting
