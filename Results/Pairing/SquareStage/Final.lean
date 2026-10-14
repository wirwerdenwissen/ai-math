module

public import Results.Pairing.SquareStage.Waste
public import Results.Pairing.SquareStage.Concrete

/-!
# A square-stage pairing with a product-region waste bound

- **Claim:** the concrete computable equivalence between `ℕ × ℕ` and `ℕ`
  has product-region span exceeding the divisor summatory function by
  `O(√A log A)`, with an explicit finite bound for every natural `A`.
- **Main declaration:** `SquareStagePairing.Final.square_waste_bigO`,
  `SquareStagePairing.Final.square_waste_finite`.
- **Not proved:** a complete bit-complexity bound for rank and unrank;
  two-sided localization for this concrete pairing; an instantiated fast
  divisor-counting algorithm; optimality or novelty of this construction.
- **Author:** avocardio (human); OpenAI Codex (GPT family).

Coordinates are zero based: `(x, y)` represents `(x + 1, y + 1)`.
For `(x + 1) * (y + 1) ≤ A`, the span is the largest assigned rank plus one
(zero for the empty region). Its cardinality is the divisor summatory
function, as proved by `ArithmeticCounting.divisorCount_eq_floor_sum`.
`Concrete.pairingEquiv` supplies the equivalence and both inverse identities.
The final bounds have no assumed quota, approximation, or coverage certificates.

## Construction

Increasing square stages allocate integer row lengths by differences of
rounded cumulative rational approximations to harmonic sums. Geometric-series
expansion on dyadic blocks and telescoping power-sum identities give an
executable evaluator. Nested finite stages define the pairing, binary searches
implement its rank and inverse, and finite hyperbola counts bound its waste.

## Attribution and limits

The product-region storage objective and its exact hyperbolic-shell optimum
are established prior work: A. L. Rosenberg, *Managing Storage for Extendible
Arrays*, SIAM J. Comput. 4(3), 1975, 287–306, Theorem 3.1 and Realization 5,
https://doi.org/10.1137/0204024. This is credit for the benchmark, not an
assertion that Rosenberg states the particular dyadic construction here.

Related enumerative-coding context is T. M. Cover, *Enumerative Source
Encoding*, IEEE Trans. Inf. Theory 19(1), 1973, 73–77,
https://isl.stanford.edu/~cover/papers/transIT/0073cove.pdf.
The formal development uses Lean and Mathlib. Geometric-series approximation
and telescoping power sums are standard ingredients. No literature-priority
claim or practical compression advantage is made. Auxiliary counting and
work-bound theorems in the supporting modules retain their explicit hypotheses;
they do not establish the omitted concrete runtime or localization results.
-/

@[expose] public section

namespace SquareStagePairing.Final
open SquareStagePairing.Concrete SquareStagePairing.ArithmeticCounting

def squareSpan (a : ℕ) : ℕ := span pairingEquiv.symm a

theorem square_span_le_stage (a : ℕ) :
    squareSpan a ≤ SquareStagePairing.Bijection.total quotas (Nat.sqrt a+2) := by
  apply Finset.sup_le
  intro p hp
  have hh := product_coverage p a ((mem_region a p).1 hp)
  exact Nat.succ_le_of_lt hh

theorem square_span_ideal (a : ℕ) :
    (squareSpan a:ℝ) ≤ SquareStagePairing.Waste.ideal (Nat.sqrt a+2) (Nat.sqrt a+2)+1 := by
  have hs := square_span_le_stage a
  have ht := total_le_ideal (Nat.sqrt a+2)
  have hs' : (squareSpan a:ℝ) ≤
      (SquareStagePairing.Bijection.total quotas (Nat.sqrt a+2):ℝ) := by exact_mod_cast hs
  have ht' : (SquareStagePairing.Bijection.total quotas (Nat.sqrt a+2):ℝ) ≤
      SquareStagePairing.Waste.ideal (Nat.sqrt a+2) (Nat.sqrt a+2)+1 := by
    have hcast := (Rat.cast_le (K := ℝ)).2 ht
    simpa only [SquareStagePairing.Harmonic.ideal, SquareStagePairing.Waste.ideal, Rat.cast_add, Rat.cast_sub,
      Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat,
      harmonic_eq_standard] using hcast
  exact hs'.trans ht'

/-- Waste of the actual concrete dyadic square-stage bijection. No
    approximation, counting, or coverage hypothesis remains. -/
theorem square_waste_bigO :
    (fun a => ((squareSpan a-divisorCount a:ℕ):ℝ))
      =O[Filter.atTop] (fun a => Real.sqrt a*Real.log a) := by
  apply SquareStagePairing.Waste.waste_bigO
  · intro a _ha
    exact square_span_ideal a
  · exact divisorCount_le_span pairingEquiv.symm

theorem square_waste_finite (a : ℕ) :
    ((squareSpan a-divisorCount a:ℕ):ℝ) ≤
      (8*(Nat.sqrt a:ℝ)+8)*(_root_.harmonic (Nat.sqrt a):ℝ)+2*Nat.sqrt a+9 := by
  apply SquareStagePairing.Waste.waste_finite (Nat.sqrt a) (squareSpan a) (divisorCount a)
  · exact square_span_ideal a
  · exact SquareStagePairing.Waste.divisor_harmonic_lower a (Nat.sqrt a) (Nat.sqrt_le a)
  · exact divisorCount_le_span pairingEquiv.symm a

end SquareStagePairing.Final
