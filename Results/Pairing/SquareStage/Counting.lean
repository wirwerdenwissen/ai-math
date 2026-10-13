module

public import Lean

/-!
# Recovering a finite support endpoint and counting with bounded holes

- **Claim:** a Boolean predicate with a certified final true position and at most
  `k` earlier false positions admits exact endpoint recovery by block queries;
  an additional initial-prefix hypothesis permits exact localized counting.
- **Main declaration:** `SquareStagePairing.Counting.exactSpan_correct`,
  `SquareStagePairing.Counting.localizedCount_correct`,
  `SquareStagePairing.Counting.localized_binary_cost`.
- **Not proved:** the certificates are hypotheses. The cost theorem is in the
  explicitly defined weighted-operation model, conditional on decoder-time and
  output-length bounds; it does not verify a compiler, a Turing-machine
  simulation, or those decoder bounds. Natural arithmetic is not assumed to
  have unit bit cost.
- **Author:** avocardio (human); OpenAI Codex (GPT family).
-/

@[expose] public section

namespace SquareStagePairing.Counting

def count (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n+1 => count p n + if p n then 1 else 0

def scan (p : Nat → Bool) (start : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => scan p start n + if p (start+n) then 1 else 0

def anyBlock (p : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => false
  | n+1 => anyBlock p start n || p (start+n)

theorem count_mono (p : Nat → Bool) (a b : Nat) (h : a ≤ b) :
    count p a ≤ count p b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst a
    exact Nat.le_refl _
  | succ b ih =>
    by_cases he : a = b+1
    · subst a; exact Nat.le_refl _
    · have hi := ih (by omega : a ≤ b)
      simp only [count]; omega

theorem scan_add (p : Nat → Bool) (start len : Nat) :
    count p (start+len) = count p start + scan p start len := by
  induction len with
  | zero => simp [scan]
  | succ len ih =>
    change count p (start+len) + (if p (start+len) then 1 else 0) = _
    rw [ih]; simp only [scan]; omega

theorem count_complement (p : Nat → Bool) (n : Nat) :
    count p n + count (fun i => !p i) n = n := by
  induction n with
  | zero => rfl
  | succ n ih => cases h : p n <;> simp [count, h] <;> omega

theorem count_zero (p : Nat → Bool) (n : Nat)
    (h : ∀ i, i < n → p i = false) : count p n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := h n (by omega)
    have hp := ih (fun i hi => h i (by omega))
    simp [count, hn, hp]

theorem scan_full (p : Nat → Bool) (start len : Nat)
    (h : ∀ i, start ≤ i → i < start+len → p i = true) :
    scan p start len = len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have hn := h (start+len) (by omega) (by omega)
    have hp := ih (fun i hi hj => h i hi (by omega))
    simp [scan, hp, hn]

theorem anyBlock_iff (p : Nat → Bool) (start len : Nat) :
    anyBlock p start len = true ↔
      ∃ i, start ≤ i ∧ i < start+len ∧ p i = true := by
  induction len with
  | zero => simp [anyBlock]; omega
  | succ len ih =>
    simp only [anyBlock, Bool.or_eq_true, ih]
    constructor
    · intro h
      rcases h with ⟨i, hi, hj, hp⟩ | hp
      · exact ⟨i, hi, by omega, hp⟩
      · exact ⟨start+len, by omega, by omega, hp⟩
    · rintro ⟨i, hi, hj, hp⟩
      by_cases he : i = start+len
      · right; simpa [he] using hp
      · left; exact ⟨i, hi, by omega, hp⟩

/-- A genuine last insider plus a bound on all preceding outsiders. -/
structure SpanCertificate (inside : Nat → Bool) (w k : Nat) : Prop where
  positive : 0 < w
  last : inside (w-1) = true
  finished : ∀ i, w ≤ i → inside i = false
  few : count (fun i => !inside i) w ≤ k

theorem block_exact (inside : Nat → Bool) (w k t : Nat)
    (h : SpanCertificate inside w k) :
    anyBlock inside t (k+1) = true ↔ t < w := by
  rw [anyBlock_iff]
  constructor
  · rintro ⟨i, hi, _, hp⟩
    by_cases ht : t < w
    · exact ht
    · have hf := h.finished i (by omega)
      simp [hf] at hp
  · intro ht
    by_cases he : w-1 < t+(k+1)
    · exact ⟨w-1, by have := h.positive; omega, he, h.last⟩
    · apply Classical.byContradiction
      intro hn
      have hf : ∀ i, t ≤ i → i < t+(k+1) → (!inside i) = true := by
        intro i hi hj
        cases hp : inside i with
        | false => rfl
        | true => exact False.elim (hn ⟨i, hi, hj, hp⟩)
      have hs := scan_full (fun i => !inside i) t (k+1) hf
      have ha := scan_add (fun i => !inside i) t (k+1)
      have hm := count_mono (fun i => !inside i) (t+(k+1)) w (by omega)
      have hh := h.few
      omega

def bitlength (n : Nat) : Nat :=
  if n = 0 then 0 else bitlength (n/2) + 1
termination_by n
decreasing_by exact Nat.div_lt_self (by omega) (by decide)

theorem lt_pow_bitlength (n : Nat) : n < 2^bitlength n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hz : n = 0
    · subst n; simp [bitlength]
    · have hi := ih (n/2) (Nat.div_lt_self (by omega) (by decide))
      rw [bitlength]
      simp only [hz, ↓reduceIte, Nat.pow_succ]
      omega

structure SearchResult where
  value : Nat
  blocks : Nat
deriving Repr, BEq

def search (query : Nat → Bool) : Nat → Nat → Nat → SearchResult
  | 0, lo, _hi => ⟨lo, 0⟩
  | fuel+1, lo, hi =>
    if lo < hi then
      let mid := (lo+hi)/2
      let r := if query mid then search query fuel (mid+1) hi
               else search query fuel lo mid
      ⟨r.value, r.blocks+1⟩
    else ⟨lo, 0⟩

theorem search_correct (query : Nat → Bool) (w fuel lo hi : Nat)
    (hq : ∀ t, query t = true ↔ t < w)
    (hl : lo ≤ w) (hu : w ≤ hi) (hs : hi-lo < 2^fuel) :
    (search query fuel lo hi).value = w := by
  induction fuel generalizing lo hi with
  | zero => simp only [Nat.pow_zero] at hs; simp only [search]; omega
  | succ fuel ih =>
    by_cases hn : lo < hi
    · have hpow := Nat.pow_succ 2 fuel
      rw [hpow] at hs
      by_cases hb : query ((lo+hi)/2) = true
      · have hm := (hq _).mp hb
        have hp := ih ((lo+hi)/2+1) hi (by omega) hu (by omega)
        simpa only [search, hn, ↓reduceIte, hb] using hp
      · have hf : query ((lo+hi)/2) = false := by
          cases hh : query ((lo+hi)/2) <;> simp_all
        have hm : ¬ (lo+hi)/2 < w := by
          intro ht; exact hb ((hq _).mpr ht)
        have hp := ih lo ((lo+hi)/2) hl (by omega) (by omega)
        simpa only [search, hn, ↓reduceIte, hf, Bool.false_eq_true] using hp
    · simp only [search, hn, ↓reduceIte]; omega

theorem search_blocks (query : Nat → Bool) (fuel lo hi : Nat) :
    (search query fuel lo hi).blocks ≤ fuel := by
  induction fuel generalizing lo hi with
  | zero => simp [search]
  | succ fuel ih =>
    by_cases hn : lo < hi
    · cases hb : query ((lo+hi)/2) <;>
        simp only [search, hn, ↓reduceIte, hb, Bool.false_eq_true]
      · have hh := ih lo ((lo+hi)/2); omega
      · have hh := ih ((lo+hi)/2+1) hi; omega
    · simp [search, hn]

def exactSpan (inside : Nat → Bool) (k upper : Nat) : SearchResult :=
  search (fun t => anyBlock inside t (k+1)) (bitlength upper) 0 upper

theorem exactSpan_correct (inside : Nat → Bool) (w k upper : Nat)
    (h : SpanCertificate inside w k) (hu : w ≤ upper) :
    (exactSpan inside k upper).value = w := by
  apply search_correct
  · intro t
    exact block_exact inside w k t h
  · exact Nat.zero_le _
  · exact hu
  · simpa using lt_pow_bitlength upper

theorem exactSpan_query_bound (inside : Nat → Bool) (k upper : Nat) :
    (exactSpan inside k upper).blocks*(k+1) ≤ bitlength upper*(k+1) :=
  Nat.mul_le_mul_right _ (search_blocks _ _ _ _)

def localizedCount (inside : Nat → Bool) (k upper : Nat) : Nat :=
  let w := (exactSpan inside k upper).value
  let start := w-2*k
  w - scan (fun i => !inside i) start (w-start)

theorem localizedCount_correct (inside : Nat → Bool) (d w k upper : Nat)
    (h : SpanCertificate inside w k) (hu : w ≤ upper)
    (hd : count inside w = d)
    (hearly : ∀ i, i < d-k → inside i = true) :
    localizedCount inside k upper = d := by
  have hc := count_complement inside w
  have hf := h.few
  have hz : count (fun i => !inside i) (w-2*k) = 0 := by
    apply count_zero
    intro i hi
    have hh := hearly i (by omega)
    simp [hh]
  have ha := scan_add (fun i => !inside i) (w-2*k) (w-(w-2*k))
  have hw : (w-2*k)+(w-(w-2*k)) = w := by omega
  rw [hw, hz] at ha
  simp only [localizedCount, exactSpan_correct inside w k upper h hu]
  omega

theorem localization_scan_bound (w k : Nat) : w-(w-2*k) ≤ 2*k := by omega

def localizedQueries (inside : Nat → Bool) (k upper : Nat) : Nat :=
  let r := exactSpan inside k upper
  r.blocks*(k+1) + (r.value-(r.value-2*k))

theorem localizedQueries_bound (inside : Nat → Bool) (k upper : Nat) :
    localizedQueries inside k upper ≤ bitlength upper*(k+1)+2*k := by
  have hs := exactSpan_query_bound inside k upper
  have ht := localization_scan_bound (exactSpan inside k upper).value k
  simp only [localizedQueries]
  omega

/-- Exact resource semantics for a full (non-short-circuit) scan. -/
def scanCost (cost : Nat → Nat) (start : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => scanCost cost start n + cost (start+n)

theorem scanCost_bound (cost : Nat → Nat) (start len q : Nat)
    (h : ∀ i, start ≤ i → i < start+len → cost i ≤ q) :
    scanCost cost start len ≤ len*q := by
  induction len with
  | zero => simp [scanCost]
  | succ len ih =>
    have hp := ih (fun i hi hj => h i hi (by omega))
    have hn := h (start+len) (by omega) (by omega)
    simp only [scanCost, Nat.add_mul, Nat.one_mul]
    omega

/-- Each branch, including the terminal branch, has a binary-control charge c.
    qcost is the full bit charge of its predicate evaluation. -/
def searchCost (query : Nat → Bool) (qcost : Nat → Nat) (c : Nat) :
    Nat → Nat → Nat → Nat
  | 0, _lo, _hi => c
  | fuel+1, lo, hi =>
    if lo < hi then
      let mid := (lo+hi)/2
      let rest := if query mid then searchCost query qcost c fuel (mid+1) hi
                  else searchCost query qcost c fuel lo mid
      rest + qcost mid + c
    else c

theorem searchCost_bound (query : Nat → Bool) (qcost : Nat → Nat)
    (c q upper fuel lo hi : Nat) (hl : lo ≤ hi) (hu : hi ≤ upper)
    (hq : ∀ t, t ≤ upper → qcost t ≤ q) :
    searchCost query qcost c fuel lo hi ≤ fuel*(q+c)+c := by
  induction fuel generalizing lo hi with
  | zero => simp [searchCost]
  | succ fuel ih =>
    by_cases hn : lo < hi
    · have hm : (lo+hi)/2 ≤ upper := by omega
      have hqc := hq _ hm
      cases hb : query ((lo+hi)/2) <;>
        simp only [searchCost, hn, ↓reduceIte, hb, Bool.false_eq_true,
          Nat.add_mul, Nat.one_mul]
      · have hp := ih lo ((lo+hi)/2) (by omega) (by omega); omega
      · have hp := ih ((lo+hi)/2+1) hi (by omega) hu; omega
    · simpa only [searchCost, hn, ↓reduceIte] using
        Nat.le_add_left c ((fuel+1)*(q+c))

/-- Full scanning is deliberately charged, even if the Boolean disjunction
    could stop early. Its cost is an upper bound for that optimization. -/
def localizedCost (inside : Nat → Bool) (membershipCost : Nat → Nat)
    (controlCost k upper : Nat) : Nat :=
  let w := (exactSpan inside k upper).value
  let start := w-2*k
  searchCost (fun t => anyBlock inside t (k+1))
      (fun t => scanCost membershipCost t (k+1)) controlCost
      (bitlength upper) 0 upper +
    scanCost membershipCost start (w-start) + 4*controlCost

theorem localizedCost_bound (inside : Nat → Bool) (membershipCost : Nat → Nat)
    (w k upper q c : Nat) (h : SpanCertificate inside w k) (hu : w ≤ upper)
    (hq : ∀ i, i ≤ upper+k → membershipCost i ≤ q) :
    localizedCost inside membershipCost c k upper ≤
      bitlength upper*((k+1)*q+c)+c+(2*k)*q+4*c := by
  have hb : ∀ t, t ≤ upper → scanCost membershipCost t (k+1) ≤ (k+1)*q := by
    intro t ht
    apply scanCost_bound
    intro i _hi hj
    apply hq; omega
  have hs := searchCost_bound (fun t => anyBlock inside t (k+1))
    (fun t => scanCost membershipCost t (k+1)) c ((k+1)*q) upper
    (bitlength upper) 0 upper (Nat.zero_le _) (Nat.le_refl _) hb
  have ht : scanCost membershipCost (w-2*k) (w-(w-2*k)) ≤ (2*k)*q := by
    have hp : scanCost membershipCost (w-2*k) (w-(w-2*k)) ≤
        (w-(w-2*k))*q := by
      apply scanCost_bound
      intro i _hi hj; apply hq; omega
    exact Nat.le_trans hp (Nat.mul_le_mul_right q (localization_scan_bound w k))
  simp only [localizedCost, exactSpan_correct inside w k upper h hu]
  omega

theorem bitlength_le (n b : Nat) (h : n < 2^b) : bitlength n ≤ b := by
  induction b generalizing n with
  | zero =>
    have : n = 0 := by simp only [Nat.pow_zero] at h; omega
    subst n
    simp [bitlength]
  | succ b ih =>
    by_cases hz : n = 0
    · subst n; simp [bitlength]
    · have hp := Nat.pow_succ 2 b
      have hh : n/2 < 2^b := by rw [hp] at h; omega
      have hi := ih (n/2) hh
      rw [bitlength]
      simp only [hz, ↓reduceIte]
      omega

/-- A conservative schoolbook binary-arithmetic charge. The constant a covers
    multiplication, comparisons, index updates and scan accumulation. The
    decoder's own time is a separate summand, never a unit-cost oracle. -/
def membershipBitCharge (decoderTime coordinateBits : Nat → Nat)
    (inputBits arithmeticConstant i : Nat) : Nat :=
  decoderTime i + arithmeticConstant*(coordinateBits i+inputBits+1)^2

theorem membershipBitCharge_bound (decoderTime coordinateBits : Nat → Nat)
    (b a i t l : Nat) (ht : decoderTime i ≤ t) (hl : coordinateBits i ≤ l) :
    membershipBitCharge decoderTime coordinateBits b a i ≤ t+a*(l+b+1)^2 := by
  have hh : coordinateBits i+b+1 ≤ l+b+1 := by omega
  have hm := Nat.mul_le_mul hh hh
  have hp : (coordinateBits i+b+1)^2 ≤ (l+b+1)^2 := by
    simpa only [Nat.pow_succ, Nat.pow_zero, Nat.one_mul] using hm
  have hc := Nat.mul_le_mul_left a hp
  simp only [membershipBitCharge]
  omega

/-- This is a theorem in an explicit weighted binary-operation model. It is
    conditional on the decoder's time and output-length bounds. It is not a
    verified compiler, Turing-machine simulation, or proof of a decoder bound. -/
theorem localized_binary_cost (inside : Nat → Bool)
    (decoderTime coordinateBits : Nat → Nat) (w k upper b a t l c : Nat)
    (h : SpanCertificate inside w k) (hu : w ≤ upper)
    (ht : ∀ i, i ≤ upper+k → decoderTime i ≤ t)
    (hl : ∀ i, i ≤ upper+k → coordinateBits i ≤ l) :
    localizedCost inside (membershipBitCharge decoderTime coordinateBits b a)
        c k upper ≤
      bitlength upper*((k+1)*(t+a*(l+b+1)^2)+c)+c+
        (2*k)*(t+a*(l+b+1)^2)+4*c := by
  apply localizedCost_bound inside _ w k upper _ c h hu
  intro i hi
  exact membershipBitCharge_bound decoderTime coordinateBits b a i t l (ht i hi) (hl i hi)

end SquareStagePairing.Counting
