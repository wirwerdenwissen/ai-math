module

public import Lean

/-!
# Pairing by nested finite row quotas

- **Claim:** row quotas satisfying the stated support, monotonicity, and
  quantitative exhaustion laws define mutually inverse rank and unrank maps,
  with each stage occupying exactly an
  initial interval of ranks; a row-coordinate bijection gives a pairing of
  natural-number pairs and a positive-coordinate variant.
- **Main declaration:** `SquareStagePairing.Bijection.pairUnrank_pairRank`,
  `SquareStagePairing.Bijection.pairRank_pairUnrank`,
  `SquareStagePairing.Bijection.prefix_characterization`.
- **Not proved:** existence or numerical accuracy of any particular quota
  system, and any runtime bound for these linear-search specifications.
- **Author:** avocardio (human); OpenAI Codex (GPT family).
-/

@[expose] public section

namespace SquareStagePairing.Bijection

def pref (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => pref f n + f n

@[simp] theorem prefix_zero (f : Nat → Nat) : pref f 0 = 0 := rfl
@[simp] theorem prefix_succ (f : Nat → Nat) (n : Nat) :
    pref f (n + 1) = pref f n + f n := rfl

theorem prefix_mono (f : Nat → Nat) {a b : Nat} (h : a ≤ b) :
    pref f a ≤ pref f b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases hab : a ≤ b
    · have h' := ih hab
      simp only [prefix_succ]
      omega
    · have : a = b + 1 := by omega
      subst a
      exact Nat.le_refl _

theorem prefix_congr (f g : Nat → Nat) (n : Nat)
    (h : ∀ i, i < n → f i = g i) : pref f n = pref g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [prefix_succ]
    rw [ih (fun i hi => h i (by omega)), h n (by omega)]

theorem prefix_add (f g : Nat → Nat) (n : Nat) :
    pref (fun i => f i + g i) n = pref f n + pref g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [prefix_succ, ih]; omega

theorem prefix_le (f g : Nat → Nat) (n : Nat)
    (h : ∀ i, i < n → f i ≤ g i) : pref f n ≤ pref g n := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have h' := ih (fun i hi => h i (by omega))
    have hn := h n (by omega)
    simp only [prefix_succ]
    omega

/-- A total bounded least search. Its executable implementation is linear;
    replacing it by binary search is a separate cost-preserving refinement. -/
def first (p : Nat → Prop) [DecidablePred p] : Nat → Nat
  | 0 => 0
  | b + 1 => if p (first p b) then first p b else b + 1

theorem first_le (p : Nat → Prop) [DecidablePred p] (b : Nat) : first p b ≤ b := by
  induction b with
  | zero => exact Nat.le_refl _
  | succ b ih => simp only [first]; split <;> omega

theorem first_min (p : Nat → Prop) [DecidablePred p] (b : Nat) :
    (∀ n, n < first p b → ¬ p n) ∧ (¬ p (first p b) → first p b = b) := by
  induction b with
  | zero =>
    constructor
    · intro n hn
      simp only [first] at hn
      omega
    · intro _
      rfl
  | succ b ih =>
    by_cases hp : p (first p b)
    · simp only [first, ite_eq_left hp]
      exact ⟨ih.1, fun h => False.elim (h hp)⟩
    · have hb := ih.2 hp
      simp only [first, ite_eq_right hp]
      constructor
      · intro n hn
        by_cases hnb : n < first p b
        · exact ih.1 n hnb
        · have : n = first p b := by omega
          subst n
          exact hp
      · intro _; exact True.intro

theorem first_spec (p : Nat → Prop) [DecidablePred p] (b : Nat)
    (hex : ∃ n, n ≤ b ∧ p n) : p (first p b) := by
  by_cases h : p (first p b)
  · exact h
  · have hb := (first_min p b).2 h
    rcases hex with ⟨n, hn, hp⟩
    by_cases hnb : n < first p b
    · exact False.elim ((first_min p b).1 n hnb hp)
    · have : n = first p b := by omega
      subst n
      exact False.elim (h hp)

theorem first_unique (p : Nat → Prop) [DecidablePred p] (b n : Nat)
    (hn : n ≤ b) (hp : p n) (hmin : ∀ i, i < n → ¬ p i) : first p b = n := by
  have hs := first_spec p b ⟨n, hn, hp⟩
  have hm := (first_min p b).1
  by_cases h : first p b < n
  · exact False.elim (hmin _ h hs)
  · by_cases h' : n < first p b
    · exact False.elim (hm _ h' hp)
    · omega

structure Quotas where
  q : Nat → Nat → Nat
  support : ∀ j m, j ≤ m → q j m = 0
  grow : ∀ j m, q j m ≤ q (j + 1) m
  cover : ∀ m k, k < q (m + k + 2) m

/-- The quota-margin theorem for positive row m+1 gives these stronger old-row
    increments. Nonnegative Nat quotas handle newly appearing rows. -/
def quotasFromGrowth (q : Nat → Nat → Nat)
    (hsupport : ∀ j m, j ≤ m → q j m = 0)
    (hgrowth : ∀ j m, m < j → q j m + 2 ≤ q (j + 1) m) : Quotas where
  q := q
  support := hsupport
  grow := by
    intro j m
    by_cases h : m < j
    · have hg := hgrowth j m h
      omega
    · have hz := hsupport j m (by omega)
      omega
  cover := by
    intro m k
    have bound : ∀ k, 2 * k + 2 ≤ q (m + k + 2) m := by
      intro k
      induction k with
      | zero =>
        have hg := hgrowth (m + 1) m (by omega)
        have heq : m + 1 + 1 = m + 2 := by omega
        rw [heq] at hg
        simp only [Nat.add_zero, Nat.mul_zero] at *
        omega
      | succ k ih =>
        have hg := hgrowth (m + k + 2) m (by omega)
        have heq : m + (k + 1) + 2 = m + k + 2 + 1 := by omega
        rw [heq]
        omega
    have hk := bound k
    omega

def total (s : Quotas) (j : Nat) : Nat := pref (s.q j) j
def added (s : Quotas) (j m : Nat) : Nat := s.q (j + 1) m - s.q j m
def delta (s : Quotas) (j m : Nat) : Nat := pref (added s j) m

theorem quota_mono (s : Quotas) {i j : Nat} (h : i ≤ j) (m : Nat) :
    s.q i m ≤ s.q j m := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact Nat.le_refl _
  | succ j ih =>
    by_cases hij : i ≤ j
    · have hi := ih hij
      have hg := s.grow j m
      omega
    · have : i = j + 1 := by omega
      subst i
      exact Nat.le_refl _

theorem prefix_plateau (s : Quotas) (j n : Nat) (h : j ≤ n) :
    pref (s.q j) n = total s j := by
  induction n with
  | zero =>
    have : j = 0 := by omega
    subst j
    rfl
  | succ n ih =>
    by_cases hjn : j ≤ n
    · simp only [prefix_succ, s.support j n hjn, Nat.add_zero]
      exact ih hjn
    · have : j = n + 1 := by omega
      subst j
      rfl

theorem total_step (s : Quotas) (j : Nat) :
    total s (j + 1) = total s j + delta s j (j + 1) := by
  have heq : pref (s.q (j + 1)) (j + 1) =
      pref (fun m => s.q j m + added s j m) (j + 1) := by
    apply prefix_congr
    intro m _
    have hg := s.grow j m
    simp only [added]
    omega
  unfold total
  rw [heq, prefix_add]
  rw [prefix_plateau s j (j + 1) (by omega)]
  rfl

theorem total_mono (s : Quotas) {i j : Nat} (h : i ≤ j) :
    total s i ≤ total s j := by
  rw [← prefix_plateau s i j h]
  exact prefix_le _ _ j (fun m _ => quota_mono s h m)

theorem total_cover (s : Quotas) (z : Nat) : z < total s (z + 2) := by
  have hq := s.cover 0 z
  simp only [Nat.zero_add] at hq
  have hp : s.q (z + 2) 0 ≤ total s (z + 2) := by
    have h := prefix_mono (s.q (z + 2)) (show 1 ≤ z + 2 by omega)
    change 0 + s.q (z + 2) 0 ≤ total s (z + 2) at h
    simpa only [Nat.zero_add] using h
  exact Nat.lt_of_lt_of_le hq hp

def entry (s : Quotas) (m k : Nat) : Nat :=
  first (fun j => k < s.q j m) (m + k + 2)

theorem entry_spec (s : Quotas) (m k : Nat) :
    k < s.q (entry s m k) m :=
  first_spec (fun j => k < s.q j m) _ ⟨m + k + 2, Nat.le_refl _, s.cover m k⟩

theorem entry_min (s : Quotas) (m k i : Nat) (h : i < entry s m k) :
    s.q i m ≤ k := by
  have hn := (first_min (fun j => k < s.q j m) (m + k + 2)).1 i h
  omega

theorem entry_row (s : Quotas) (m k : Nat) : m < entry s m k := by
  have hp := entry_spec s m k
  by_cases h : entry s m k ≤ m
  · have hs := s.support (entry s m k) m h
    omega
  · omega

def epoch (s : Quotas) (z : Nat) : Nat :=
  first (fun j => z < total s j) (z + 2) - 1

theorem epoch_interval (s : Quotas) (z : Nat) :
    total s (epoch s z) ≤ z ∧ z < total s (epoch s z + 1) := by
  let e := first (fun j => z < total s j) (z + 2)
  have he : z < total s e := first_spec (fun j => z < total s j) _
    ⟨z + 2, Nat.le_refl _, total_cover s z⟩
  have hepos : 0 < e := by
    by_cases h : e = 0
    · simp only [h, total, prefix_zero] at he
      omega
    · omega
  have hm := (first_min (fun j => z < total s j) (z + 2)).1 (e - 1) (by omega)
  change total s (e - 1) ≤ z ∧ z < total s (e - 1 + 1)
  have heq : e - 1 + 1 = e := by omega
  rw [heq]
  exact ⟨by omega, he⟩

def rowAt (s : Quotas) (j r : Nat) : Nat :=
  first (fun m => r < delta s j (m + 1)) j

theorem rowAt_interval (s : Quotas) (j r : Nat)
    (hr : r < delta s j (j + 1)) :
    rowAt s j r ≤ j ∧ delta s j (rowAt s j r) ≤ r ∧
      r < delta s j (rowAt s j r + 1) := by
  have hs := first_spec (fun m => r < delta s j (m + 1)) j ⟨j, Nat.le_refl _, hr⟩
  have hl := first_le (fun m => r < delta s j (m + 1)) j
  have hlo : delta s j (rowAt s j r) ≤ r := by
    cases hm : rowAt s j r with
    | zero => simp [delta]
    | succ m =>
      have hmin := (first_min (fun n => r < delta s j (n + 1)) j).1 m
      have hlt : m < first (fun n => r < delta s j (n + 1)) j := by
        change m < rowAt s j r
        omega
      have hn := hmin hlt
      omega
  exact ⟨hl, hlo, hs⟩

def rank (s : Quotas) (p : Nat × Nat) : Nat :=
  let j := entry s p.1 p.2 - 1
  total s j + delta s j p.1 + (p.2 - s.q j p.1)

def unrank (s : Quotas) (z : Nat) : Nat × Nat :=
  let j := epoch s z
  let r := z - total s j
  let m := rowAt s j r
  (m, s.q j m + (r - delta s j m))

theorem epoch_unique (s : Quotas) (z j : Nat)
    (hlo : total s j ≤ z) (hhi : z < total s (j + 1)) : epoch s z = j := by
  rcases epoch_interval s z with ⟨he0, he1⟩
  by_cases h : epoch s z < j
  · have ht := total_mono s (show epoch s z + 1 ≤ j by omega)
    omega
  · by_cases h' : j < epoch s z
    · have ht := total_mono s (show j + 1 ≤ epoch s z by omega)
      omega
    · omega

theorem entry_unique (s : Quotas) (m k j : Nat)
    (hlo : s.q j m ≤ k) (hhi : k < s.q (j + 1) m) : entry s m k = j + 1 := by
  have he := entry_spec s m k
  by_cases h : entry s m k ≤ j
  · have hq := quota_mono s h m
    omega
  · by_cases h' : j + 1 < entry s m k
    · have hq := entry_min s m k (j + 1) h'
      omega
    · omega

theorem rowAt_unique (s : Quotas) (j r m : Nat)
    (hr : r < delta s j (j + 1))
    (hlo : delta s j m ≤ r) (hhi : r < delta s j (m + 1)) : rowAt s j r = m := by
  rcases rowAt_interval s j r hr with ⟨_, he0, he1⟩
  by_cases h : rowAt s j r < m
  · have hd := prefix_mono (added s j) (show rowAt s j r + 1 ≤ m by omega)
    change delta s j (rowAt s j r + 1) ≤ delta s j m at hd
    omega
  · by_cases h' : m < rowAt s j r
    · have hd := prefix_mono (added s j) (show m + 1 ≤ rowAt s j r by omega)
      change delta s j (m + 1) ≤ delta s j (rowAt s j r) at hd
      omega
    · omega

theorem rank_from_interval (s : Quotas) (m k j : Nat)
    (hlo : s.q j m ≤ k) (hhi : k < s.q (j + 1) m) :
    rank s (m, k) = total s j + delta s j m + (k - s.q j m) := by
  have he := entry_unique s m k j hlo hhi
  simp only [rank, he, Nat.add_sub_cancel]

theorem row_rank_interval (s : Quotas) (m k j : Nat)
    (hlo : s.q j m ≤ k) (hhi : k < s.q (j + 1) m) :
    delta s j m ≤ delta s j m + (k - s.q j m) ∧
    delta s j m + (k - s.q j m) < delta s j (m + 1) := by
  have hg := s.grow j m
  change _ ∧ _ < delta s j m + (s.q (j + 1) m - s.q j m)
  omega

theorem stage_rank_interval (s : Quotas) (m k j : Nat)
    (hlo : s.q j m ≤ k) (hhi : k < s.q (j + 1) m) :
    total s j ≤ rank s (m, k) ∧ rank s (m, k) < total s (j + 1) := by
  have hm : m ≤ j := by
    by_cases h : j + 1 ≤ m
    · have hz := s.support (j + 1) m h
      omega
    · omega
  have hr := (row_rank_interval s m k j hlo hhi).2
  have hd := prefix_mono (added s j) (show m + 1 ≤ j + 1 by omega)
  change delta s j (m + 1) ≤ delta s j (j + 1) at hd
  rw [rank_from_interval s m k j hlo hhi, total_step]
  omega

theorem unrank_rank (s : Quotas) (p : Nat × Nat) : unrank s (rank s p) = p := by
  rcases p with ⟨m, k⟩
  let j := entry s m k - 1
  have hepos := entry_row s m k
  have heq : j + 1 = entry s m k := by omega
  have hlo : s.q j m ≤ k := entry_min s m k j (by omega)
  have hhi : k < s.q (j + 1) m := by rw [heq]; exact entry_spec s m k
  have hf := rank_from_interval s m k j hlo hhi
  rcases stage_rank_interval s m k j hlo hhi with ⟨hn0, hn1⟩
  have hep := epoch_unique s (rank s (m, k)) j hn0 hn1
  have hr : rank s (m, k) - total s j = delta s j m + (k - s.q j m) := by omega
  have hb := row_rank_interval s m k j hlo hhi
  have htot := total_step s j
  have hrow := rowAt_unique s j (rank s (m, k) - total s j) m
    (by omega) (by omega) (by omega)
  simp only [unrank, hep, hrow]
  congr 1
  omega

theorem rank_unrank (s : Quotas) (z : Nat) : rank s (unrank s z) = z := by
  let j := epoch s z
  let r := z - total s j
  let m := rowAt s j r
  rcases epoch_interval s z with ⟨hn0, hn1⟩
  change total s j ≤ z at hn0
  change z < total s (j + 1) at hn1
  have htot := total_step s j
  have hr : r < delta s j (j + 1) := by
    change z - total s j < delta s j (j + 1)
    omega
  rcases rowAt_interval s j r hr with ⟨_, hr0, hr1⟩
  change delta s j m ≤ r at hr0
  let k := s.q j m + (r - delta s j m)
  have hlo : s.q j m ≤ k := by omega
  have hhi : k < s.q (j + 1) m := by
    have hg := s.grow j m
    change r < delta s j m + (s.q (j + 1) m - s.q j m) at hr1
    change s.q j m + (r - delta s j m) < s.q (j + 1) m
    omega
  change rank s (m, k) = z
  rw [rank_from_interval s m k j hlo hhi]
  dsimp only [k, r] at *
  omega

/-- Membership in the j-th finite stage is exactly membership in the first N_j ranks. -/
theorem prefix_characterization (s : Quotas) (j m k : Nat) :
    rank s (m, k) < total s j ↔ k < s.q j m := by
  let e := entry s m k
  have hep : 0 < e := by have := entry_row s m k; omega
  have hlo := entry_min s m k (e - 1) (by omega)
  have hhi : k < s.q (e - 1 + 1) m := by
    have heq : e - 1 + 1 = e := by omega
    rw [heq]
    exact entry_spec s m k
  rcases stage_rank_interval s m k (e - 1) hlo hhi with ⟨hf0, hf1⟩
  constructor
  · intro h
    have hej : e ≤ j := by
      by_cases h' : j ≤ e - 1
      · have ht := total_mono s h'
        omega
      · omega
    have hq := quota_mono s hej m
    have hs := entry_spec s m k
    change k < s.q e m at hs
    omega
  · intro h
    have hej : e ≤ j := by
      by_cases h' : j < e
      · have hq := entry_min s m k j h'
        omega
      · omega
    have ht := total_mono s (show e - 1 + 1 ≤ j by omega)
    omega

theorem nested_stages (s : Quotas) (j m k : Nat) (h : k < s.q j m) :
    k < s.q (j + 1) m := by have hg := s.grow j m; omega

theorem exhaustion (s : Quotas) (m k : Nat) : ∃ j, k < s.q j m :=
  ⟨m + k + 2, s.cover m k⟩

/-- The input coordinates here are zero based; add one to each to obtain the
    positive-coordinate convention used in the research notes. -/
def rowEncode (p : Nat × Nat) : Nat × Nat :=
  if p.1 < p.2 then (p.1, 2 * (p.2 - p.1) - 1)
  else (p.2, 2 * (p.1 - p.2))

def rowDecode (p : Nat × Nat) : Nat × Nat :=
  if p.2 % 2 = 0 then (p.1 + p.2 / 2, p.1)
  else (p.1, p.1 + (p.2 + 1) / 2)

theorem rowDecode_encode (p : Nat × Nat) : rowDecode (rowEncode p) = p := by
  rcases p with ⟨x, y⟩
  by_cases hxy : x < y
  · have hodd : (2 * (y - x) - 1) % 2 ≠ 0 := by omega
    simp only [rowEncode, hxy, ite_eq_left, rowDecode, hodd, ite_false]
    congr 1
    omega
  · have heven : (2 * (x - y)) % 2 = 0 := by omega
    simp only [rowEncode, hxy, ite_false, rowDecode, heven, ite_true]
    congr 1
    omega

theorem rowEncode_decode (p : Nat × Nat) : rowEncode (rowDecode p) = p := by
  rcases p with ⟨m, k⟩
  by_cases hk : k % 2 = 0
  · have hnot : ¬ m + k / 2 < m := by omega
    simp only [rowDecode, hk, ite_eq_left, rowEncode, hnot, ite_false]
    congr 1
    omega
  · have hyes : m < m + (k + 1) / 2 := by omega
    simp only [rowDecode, hk, ite_false, rowEncode, hyes, ite_eq_left]
    congr 1
    omega

def pairRank (s : Quotas) (p : Nat × Nat) : Nat := rank s (rowEncode p)
def pairUnrank (s : Quotas) (z : Nat) : Nat × Nat := rowDecode (unrank s z)

theorem pairUnrank_pairRank (s : Quotas) (p : Nat × Nat) :
    pairUnrank s (pairRank s p) = p := by
  simp only [pairUnrank, pairRank, unrank_rank, rowDecode_encode]

theorem pairRank_pairUnrank (s : Quotas) (z : Nat) :
    pairRank s (pairUnrank s z) = z := by
  simp only [pairUnrank, pairRank, rowEncode_decode, rank_unrank]

theorem quota_le_total (s : Quotas) (j m : Nat) : s.q j m ≤ total s j := by
  by_cases hm : m < j
  · have hp := prefix_mono (s.q j) (show m + 1 ≤ j by omega)
    change pref (s.q j) m + s.q j m ≤ total s j at hp
    omega
  · rw [s.support j m (by omega)]
    omega

theorem epoch_le_rank (s : Quotas) (z : Nat) : epoch s z ≤ z + 1 := by
  have h := first_le (fun j => z < total s j) (z + 2)
  unfold epoch
  omega

theorem unrank_position_bounds (s : Quotas) (z : Nat) :
    (unrank s z).1 ≤ z + 1 ∧ (unrank s z).2 ≤ z := by
  let j := epoch s z
  let r := z - total s j
  let m := rowAt s j r
  have hj := epoch_le_rank s z
  change j ≤ z + 1 at hj
  rcases epoch_interval s z with ⟨h0, h1⟩
  change total s j ≤ z at h0
  change z < total s (j + 1) at h1
  have hs := total_step s j
  have hr : r < delta s j (j + 1) := by dsimp only [r]; omega
  have hm := (rowAt_interval s j r hr).1
  change m ≤ j at hm
  have hq := quota_le_total s j m
  change m ≤ z + 1 ∧ s.q j m + (r - delta s j m) ≤ z
  dsimp only [r]
  omega

theorem rowDecode_bounds (m k : Nat) :
    (rowDecode (m, k)).1 ≤ m + k ∧ (rowDecode (m, k)).2 ≤ m + k := by
  by_cases hk : k % 2 = 0
  · simp only [rowDecode, ite_eq_left hk]
    omega
  · simp only [rowDecode, ite_eq_right hk]
    omega

theorem positive_coordinate_bounds (s : Quotas) (z : Nat) :
    (pairUnrank s z).1 + 1 ≤ 2 * z + 2 ∧
    (pairUnrank s z).2 + 1 ≤ 2 * z + 2 := by
  have hp := unrank_position_bounds s z
  have hd := rowDecode_bounds (unrank s z).1 (unrank s z).2
  cases he : unrank s z with
  | mk m k =>
    simp only [he, pairUnrank] at *
    omega

def PositivePair := {p : Nat × Nat // 0 < p.1 ∧ 0 < p.2}

def toPositive (p : Nat × Nat) : PositivePair :=
  ⟨(p.1 + 1, p.2 + 1), by constructor <;> omega⟩

def fromPositive (p : PositivePair) : Nat × Nat := (p.val.1 - 1, p.val.2 - 1)

theorem fromPositive_toPositive (p : Nat × Nat) : fromPositive (toPositive p) = p := by
  rcases p with ⟨x, y⟩
  simp [fromPositive, toPositive]

theorem toPositive_fromPositive (p : PositivePair) : toPositive (fromPositive p) = p := by
  apply Subtype.ext
  rcases p with ⟨⟨x, y⟩, hx, hy⟩
  change (x - 1 + 1, y - 1 + 1) = (x, y)
  congr 1 <;> omega

def positiveRank (s : Quotas) (p : PositivePair) : Nat := pairRank s (fromPositive p)
def positiveUnrank (s : Quotas) (z : Nat) : PositivePair := toPositive (pairUnrank s z)

theorem positiveUnrank_positiveRank (s : Quotas) (p : PositivePair) :
    positiveUnrank s (positiveRank s p) = p := by
  simp only [positiveUnrank, positiveRank, pairUnrank_pairRank, toPositive_fromPositive]

theorem positiveRank_positiveUnrank (s : Quotas) (z : Nat) :
    positiveRank s (positiveUnrank s z) = z := by
  simp only [positiveUnrank, positiveRank, fromPositive_toPositive, pairRank_pairUnrank]

end SquareStagePairing.Bijection
