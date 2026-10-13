module

public import Results.Pairing.SquareStage.Bijection
public import Results.Pairing.SquareStage.Counting

/-!
# Binary-search refinement of quota-stage rank and unrank

- **Claim:** binary searches and a cumulative-quota evaluator reproduce the
  generic rank and unrank functions and their two inverse identities; each
  individual bounded binary search uses at most the bound's bit length in
  predicate calls.
- **Main declaration:** `SquareStagePairing.Bijection.fastUnrank_fastRank`,
  `SquareStagePairing.Bijection.fastRank_fastUnrank`,
  `SquareStagePairing.Bijection.firstBinary_calls`.
- **Not proved:** the cost of evaluating the cumulative quotas or predicates,
  or a complete bit-complexity bound for rank or unrank.
- **Author:** avocardio (human); OpenAI Codex (GPT family).
-/

@[expose] public section

namespace SquareStagePairing.Bijection

def firstBinary (p : Nat → Prop) [DecidablePred p] (bound : Nat) : Nat :=
  (SquareStagePairing.Counting.search (fun t => decide (¬ p t))
    (SquareStagePairing.Counting.bitlength bound) 0 bound).value

theorem firstBinary_eq_first (p : Nat → Prop) [DecidablePred p] (bound : Nat)
    (hp : p bound) (hm : ∀ i j, i ≤ j → p i → p j) :
    firstBinary p bound = first p bound := by
  let w := first p bound
  have hw := first_spec p bound ⟨bound, Nat.le_refl _, hp⟩
  have hq : ∀ t, decide (¬ p t) = true ↔ t < w := by
    intro t
    simp only [decide_eq_true_eq]
    constructor
    · intro hn
      by_cases ht : w ≤ t
      · exact False.elim (hn (hm w t ht hw))
      · omega
    · intro ht
      exact (first_min p bound).1 t ht
  exact SquareStagePairing.Counting.search_correct _ w _ 0 bound hq (by omega)
    (first_le p bound) (by simpa using SquareStagePairing.Counting.lt_pow_bitlength bound)

theorem firstBinary_calls (p : Nat → Prop) [DecidablePred p] (bound : Nat) :
    (SquareStagePairing.Counting.search (fun t => decide (¬ p t))
      (SquareStagePairing.Counting.bitlength bound) 0 bound).blocks ≤ SquareStagePairing.Counting.bitlength bound :=
  SquareStagePairing.Counting.search_blocks _ _ _ _

/-- An efficiently evaluable cumulative quota can replace the linear sum
    specification. Complexity of evaluating Q is an obligation of the instance. -/
structure Cumulative (s : Quotas) where
  Q : Nat → Nat → Nat
  zero : ∀ j, Q j 0 = 0
  step : ∀ j m, Q j (m + 1) = Q j m + s.q j m

theorem cumulative_eq_pref (s : Quotas) (c : Cumulative s) (j m : Nat) :
    c.Q j m = pref (s.q j) m := by
  induction m with
  | zero => exact c.zero j
  | succ m ih => rw [c.step, ih]; rfl

def fastTotal (s : Quotas) (c : Cumulative s) (j : Nat) : Nat := c.Q j j
def fastDelta (s : Quotas) (c : Cumulative s) (j m : Nat) : Nat :=
  c.Q (j + 1) m - c.Q j m

theorem fastTotal_eq (s : Quotas) (c : Cumulative s) (j : Nat) :
    fastTotal s c j = total s j := cumulative_eq_pref s c j j

theorem fastDelta_eq (s : Quotas) (c : Cumulative s) (j m : Nat) :
    fastDelta s c j m = delta s j m := by
  have hs : pref (s.q (j + 1)) m = pref (s.q j) m + delta s j m := by
    have he : pref (s.q (j + 1)) m =
        pref (fun i => s.q j i + added s j i) m := by
      apply prefix_congr
      intro i _
      have hg := s.grow j i
      simp only [added]
      omega
    rw [he, prefix_add]
    rfl
  simp only [fastDelta, cumulative_eq_pref]
  omega

def fastEntry (s : Quotas) (m k : Nat) : Nat :=
  firstBinary (fun j => k < s.q j m) (m + k + 2)

theorem fastEntry_eq (s : Quotas) (m k : Nat) : fastEntry s m k = entry s m k := by
  apply firstBinary_eq_first
  · exact s.cover m k
  · intro i j hij h
    have hq := quota_mono s hij m
    omega

def fastEpoch (s : Quotas) (c : Cumulative s) (z : Nat) : Nat :=
  firstBinary (fun j => z < fastTotal s c j) (z + 2) - 1

theorem fastEpoch_eq (s : Quotas) (c : Cumulative s) (z : Nat) :
    fastEpoch s c z = epoch s z := by
  simp only [fastEpoch, fastTotal_eq, epoch]
  rw [firstBinary_eq_first]
  · exact total_cover s z
  · intro i j hij h
    have ht := total_mono s hij
    omega

def fastRow (s : Quotas) (c : Cumulative s) (j r : Nat) : Nat :=
  firstBinary (fun m => r < fastDelta s c j (m + 1)) j

theorem fastRow_eq (s : Quotas) (c : Cumulative s) (j r : Nat)
    (hr : r < delta s j (j + 1)) : fastRow s c j r = rowAt s j r := by
  simp only [fastRow, fastDelta_eq, rowAt]
  apply firstBinary_eq_first
  · exact hr
  · intro a b hab ha
    have hd := prefix_mono (added s j) (show a + 1 ≤ b + 1 by omega)
    change delta s j (a + 1) ≤ delta s j (b + 1) at hd
    omega

def fastRank (s : Quotas) (c : Cumulative s) (p : Nat × Nat) : Nat :=
  let j := fastEntry s p.1 p.2 - 1
  fastTotal s c j + fastDelta s c j p.1 + (p.2 - s.q j p.1)

theorem fastRank_eq (s : Quotas) (c : Cumulative s) (p : Nat × Nat) :
    fastRank s c p = rank s p := by
  simp only [fastRank, fastEntry_eq, fastTotal_eq, fastDelta_eq, rank]

def fastUnrank (s : Quotas) (c : Cumulative s) (z : Nat) : Nat × Nat :=
  let j := fastEpoch s c z
  let r := z - fastTotal s c j
  let m := fastRow s c j r
  (m, s.q j m + (r - fastDelta s c j m))

theorem fastUnrank_eq (s : Quotas) (c : Cumulative s) (z : Nat) :
    fastUnrank s c z = unrank s z := by
  rcases epoch_interval s z with ⟨h0, h1⟩
  have hs := total_step s (epoch s z)
  have hr : z - total s (epoch s z) < delta s (epoch s z) (epoch s z + 1) := by omega
  simp only [fastUnrank, fastEpoch_eq, fastTotal_eq,
    fastRow_eq s c _ _ hr, fastDelta_eq, unrank]

theorem fastUnrank_fastRank (s : Quotas) (c : Cumulative s) (p : Nat × Nat) :
    fastUnrank s c (fastRank s c p) = p := by
  rw [fastRank_eq, fastUnrank_eq, unrank_rank]

theorem fastRank_fastUnrank (s : Quotas) (c : Cumulative s) (z : Nat) :
    fastRank s c (fastUnrank s c z) = z := by
  rw [fastUnrank_eq, fastRank_eq, rank_unrank]

end SquareStagePairing.Bijection
