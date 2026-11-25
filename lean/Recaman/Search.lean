module

public import Recaman.Dial

/-!
# A small search: `R 13 ≤ 3` and `R 28 ≤ 4`

Write `A t = ∑_{i < t} u i`.  A visit of height `x` at time `s` leaves the **label** `A s - x s` on height `x`, and time
`s` witnesses the step after `t` iff `u t = x + 1` and the label `A t - x t + 1` is on height `x`.  So a play is
determined by what it does at the heights `≤ 1`, and heights `≤ 0` matter only through their duration and area: an
excursion below `1` lasting `2 k + 2` steps has area `1 - (k + 2 j)` with `k + 2 j ≤ k ^ 2` (`excursion`).

`ok` runs through all plays, branching over `(k, j)`, and cuts a branch as soon as the dip bound `Play.le_of_dip` and a
table of known reaches settle it.  To be evaluated by the kernel it works with natural numbers: the state holds the time
`n = L - t` that remains, the area as `A + L²`, and labels as `A + L² + x n`.
-/

@[expose] public section

namespace Recaman

open Finset

/-- `force n k = k n`, but the kernel evaluates `n` first. -/
def force {α : Type} (n : ℕ) (k : ℕ → α) : α :=
  match n with
  | 0 => k 0
  | n + 1 => k n.succ

@[simp] theorem force_eq {α : Type} (n : ℕ) (k : ℕ → α) : force n k = k n := by cases n <;> rfl

/-- Is `(x, y)` on the list? -/
def hit (x y : ℕ) : List (ℕ × ℕ) → Bool
  | [] => false
  | (a, b) :: l => (cond (Nat.beq a x) (Nat.beq b y) false).or (hit x y l)

theorem hit_iff {x y : ℕ} {l : List (ℕ × ℕ)} : hit x y l = true ↔ (x, y) ∈ l := by
  induction l with
  | nil => simp [hit]
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    rw [hit, Bool.or_eq_true, ih, List.mem_cons, Prod.mk.injEq, Bool.cond_false_right, Bool.and_eq_true, Nat.beq_eq,
      Nat.beq_eq, eq_comm, @eq_comm _ b]

def allBelow : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n + 1, p => (p n).and (allBelow n p)

theorem allBelow_spec {n : ℕ} {p : ℕ → Bool} (h : allBelow n p = true) : ∀ k < n, p k = true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [allBelow, Bool.and_eq_true] at h
    intro k hk
    rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with hk | rfl
    exacts [ih h.2 k hk, h.1]

/-! The next functions use the raw operations of `ℕ`, which the kernel evaluates fast; `node_eq` restates them. -/

/-- Can the dip bound conclude, with `n` steps left, at height `x`, after a maximum `m`? -/
def cut (H : ℕ) (r : ℕ → ℕ) (n x m : ℕ) : Bool := Nat.ble (m.add (r (n.sub (m.sub x)))) H

/-- The step from a height `x ≥ 2` is forced: up iff its label is there. -/
def high (go : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ) → Bool) (n x A m : ℕ) (l l' : List (ℕ × ℕ)) : Bool :=
  go (n.sub (nat_lit 1)) (cond (hit (x.sub (nat_lit 1)) (Nat.succ (A.add ((x.sub (nat_lit 1)).mul n))) l) x.succ
    (x.sub (nat_lit 1))) (A.add x) m l'

/-- From height `1` the play steps up, or makes an excursion of `2 k + 2` steps below `1`. -/
def low (H : ℕ) (r : ℕ → ℕ) (go : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ) → Bool) (n A m : ℕ) (l' : List (ℕ × ℕ)) : Bool :=
  (go (n.sub (nat_lit 1)) (nat_lit 2) A.succ m l').and (allBelow (n.div (nat_lit 2)) fun k =>
    (cut H r (n.sub ((k.add k).add (nat_lit 2))) (nat_lit 1) m).or
      (allBelow (((k.mul k).sub k).div (nat_lit 2)).succ fun j =>
        go (n.sub ((k.add k).add (nat_lit 2))) (nat_lit 1) (A.succ.sub (k.add (j.add j))) m l'))

def move (H : ℕ) (r : ℕ → ℕ) (go : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ) → Bool) (n x A m : ℕ) (l l' : List (ℕ × ℕ)) : Bool :=
  cond (Nat.ble (nat_lit 2) x) (high go n x A m l l') (low H r go n A m l')

/-- With `n` steps left, the play stands at height `x`, with area `A`, maximum `m` and labels `l`.  Does it stay at or
below `H`?  Ask `go` for the next positions. -/
def node (H : ℕ) (r : ℕ → ℕ) (go : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ) → Bool) (n x A m : ℕ) (l : List (ℕ × ℕ)) : Bool :=
  force n fun n => force x fun x => force A fun A => force (cond (Nat.ble m x) x m) fun m =>
    (Nat.ble m H).and ((cut H r n x m).or (force (A.add (x.mul n)) fun y => move H r go n x A m l ((x, y) :: l)))

theorem node_eq (H : ℕ) (r : ℕ → ℕ) (go : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ) → Bool) (n x A m : ℕ) (l : List (ℕ × ℕ)) :
    node H r go n x A m l = (let m := bif Nat.ble m x then x else m
      let l' := (x, A + x * n) :: l
      Nat.ble m H && (cut H r n x m || bif Nat.ble 2 x then
        go (n - 1) (bif hit (x - 1) (A + (x - 1) * n + 1) l then x + 1 else x - 1) (A + x) m l'
      else go (n - 1) 2 (A + 1) m l' && allBelow (n / 2) fun k => cut H r (n - (k + k + 2)) 1 m ||
        allBelow ((k * k - k) / 2 + 1) fun j => go (n - (k + k + 2)) 1 (A + 1 - (k + (j + j))) m l')) := by
  simp only [node, force_eq]; rfl

/-- The search, to depth `f`. -/
noncomputable def ok (H : ℕ) (r : ℕ → ℕ) (f : ℕ) : ℕ → ℕ → ℕ → ℕ → List (ℕ × ℕ) → Bool :=
  Nat.rec (fun _ _ _ _ _ => false) (fun _ => node H r) f

theorem ok_succ (H : ℕ) (r : ℕ → ℕ) (f n x A m : ℕ) (l : List (ℕ × ℕ)) :
    ok H r (f + 1) n x A m l = node H r (ok H r f) n x A m l := rfl

/-! ## Excursions below height `1` -/

theorem sum_min (m : ℕ) : ∑ i ∈ range (2 * m + 1), min i (2 * m - i) = m * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ',
      sum_congr rfl (g := fun i => min i (2 * m - i) + 1) (fun i hi => by have := mem_range.mp hi; omega),
      sum_add_distrib, ih]
    simp only [sum_const, card_range, smul_eq_mul, mul_one]
    have : min (2 * m + 1 + 1) (2 * (m + 1) - (2 * m + 1 + 1)) = 0 := by omega
    rw [this]; simp; ring

theorem sum_pairs {u : ℕ → ℤ} (h : Walk u) (s k : ℕ) (hu : ∀ i < 2 * k, u (s + i) ≤ 0) :
    ∃ j : ℕ, ∑ i ∈ range (2 * k), u (s + i) = -(k + 2 * j : ℕ) := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨j, hj⟩ := ih fun i hi => hu i (by omega)
    have h1 := hu (2 * k) (by omega); have h2 := hu (2 * k + 1) (by omega); have h3 := h (s + 2 * k)
    rw [← add_assoc] at h2
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, sum_range_succ, sum_range_succ, hj, ← add_assoc]
    rcases h3 with e | e
    · exact ⟨j + (-u (s + 2 * k) - 1).toNat, by push_cast; omega⟩
    · exact ⟨j + (-u (s + 2 * k)).toNat, by push_cast; omega⟩

theorem parity {u : ℕ → ℤ} (h : Walk u) (s d : ℕ) : (u (s + d) - u s - d) % 2 = 0 := by
  induction d with
  | zero => simp
  | succ d ih => have := h (s + d); rw [← add_assoc]; push_cast; omega

theorem excursion {u : ℕ → ℤ} (h : Walk u) {t : ℕ} (h0 : u t = 1) (h1 : u (t + 1) = 0) (L : ℕ) :
    (∀ i, t < i → i ≤ L → u i ≤ 0) ∨ ∃ k j, t + 2 * k + 2 ≤ L ∧ u (t + 2 * k + 2) = 1 ∧
      (∀ i, t < i → i < t + 2 * k + 2 → u i ≤ 0) ∧ j ≤ (k * k - k) / 2 ∧
      ∑ i ∈ Ico t (t + 2 * k + 2), u i = 1 - (k + 2 * j : ℕ) := by
  by_cases hex : ∃ d, 1 ≤ u (t + 1 + d) ∧ t + 1 + d ≤ L
  swap
  · left; intro i hi hL
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show t + 1 ≤ i by omega)
    by_contra hc; exact hex ⟨d, by omega, hL⟩
  right
  classical
  obtain ⟨hd, hL⟩ := Nat.find_spec hex
  have hmin := fun i => Nat.find_min hex (m := i)
  set d := Nat.find hex
  have hneg : ∀ i < d, u (t + 1 + i) ≤ 0 := fun i hi => by
    by_contra hc; exact hmin i hi ⟨by omega, by omega⟩
  obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by
    have : d ≠ 0 := fun h => by rw [h, add_zero] at hd; omega
    omega⟩
  have hlast := hneg e (by omega)
  have hst := h (t + 1 + e)
  rw [he, ← add_assoc] at hd
  have hp := parity h (t + 1) e
  obtain ⟨k, rfl⟩ : ∃ k, e = 2 * k := ⟨e / 2, by omega⟩
  obtain ⟨j, hj⟩ := sum_pairs h (t + 1 + 1) k fun i hi => by
    have := hneg (1 + i) (by omega); rwa [← add_assoc] at this
  have hs : ∑ i ∈ range (2 * k + 1), u (t + 1 + i) = -(k + 2 * j : ℕ) := by
    rw [sum_range_succ', add_zero, h1, add_zero, ← hj]
    exact sum_congr rfl fun i _ => by rw [add_assoc (t + 1), add_comm 1 i]
  have hlow : -((k * k : ℕ) : ℤ) ≤ -(k + 2 * j : ℕ) := by
    rw [← hs, ← sum_min, Nat.cast_sum, ← sum_neg_distrib]
    refine sum_le_sum fun i hi => ?_
    have hi := mem_range.mp hi
    have b1 := abs_le.mp (le_add_of_step h (t + 1) i)
    have b2 := abs_le.mp (le_add_of_step h (t + 1 + i) (2 * k - i))
    rw [add_assoc, Nat.add_sub_cancel' (by omega)] at b2
    push_cast [Nat.cast_sub (show i ≤ 2 * k by omega)] at b2 ⊢
    omega
  refine ⟨k, j, by omega, ?_, fun i hi hi' => ?_, by omega, ?_⟩
  · rw [show t + 2 * k + 2 = t + 1 + 2 * k + 1 by ring]; omega
  · obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (show t + 1 ≤ i by omega)
    exact hneg i (by omega)
  · rw [sum_Ico_eq_sum_range, show t + 2 * k + 2 - t = 2 * k + 1 + 1 by omega, sum_range_succ', add_zero, h0,
      sum_congr rfl (g := fun i => u (t + 1 + i)) (fun i _ => by rw [add_assoc, add_comm 1 i]), hs]
    ring

/-! ## Soundness -/

/-- The area before time `t`, shifted by `L²` to be a natural number. -/
def area (L : ℕ) (u : ℕ → ℤ) (t : ℕ) : ℕ := (∑ i ∈ range t, u i + L * L).toNat

theorem area_cast {L : ℕ} {u : ℕ → ℤ} (h : Walk u) (h0 : u 0 = 0) {t : ℕ} (ht : t ≤ L) :
    (area L u t : ℤ) = ∑ i ∈ range t, u i + L * L := by
  have h1 := (abs_le.mp (show |∑ i ∈ range t, u i| ≤ t * t by
    have := area_bound h 0 t
    simp only [h0, sub_zero, zero_add, ← range_eq_Ico] at this
    nlinarith [abs_nonneg (∑ i ∈ range t, u i)])).1
  have h2 : (t : ℤ) * t ≤ L * L := by gcongr
  exact Int.toNat_of_nonneg (by linarith)

/-- `l` is the list of labels written on the heights `≥ 1` before time `t`. -/
def Labels (L : ℕ) (u : ℕ → ℤ) (t : ℕ) (l : List (ℕ × ℕ)) : Prop :=
  ∀ x y : ℕ, 1 ≤ x → ((x, y) ∈ l ↔ ∃ s < t, u s = x ∧ area L u s + x * (L - s) = y)

theorem Labels.witness {L t x : ℕ} {u : ℕ → ℤ} {l : List (ℕ × ℕ)} (h : Labels L u t l) (hu : Walk u) (h0 : u 0 = 0)
    (ht : t ≤ L) (hx : u t = x) (h2 : 2 ≤ x) :
    hit (x - 1) (area L u t + (x - 1) * (L - t) + 1) l = true ↔ ∃ s < t, Wit u s t := by
  rw [hit_iff, h _ _ (by omega)]
  refine exists_congr fun s => and_congr_right fun hs => ?_
  have e : ∑ i ∈ Ico s t, (u i - u s) = ∑ i ∈ range t, u i - ∑ i ∈ range s, u i - (t - s) * u s := by
    rw [sum_sub_distrib, sum_Ico_eq_sub _ hs.le, sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hs.le]
  have a1 := area_cast hu h0 ht
  have a2 := area_cast hu h0 (hs.le.trans ht)
  unfold Wit
  rw [e, hx]
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le' (show 1 ≤ x by omega)
  rw [Nat.add_sub_cancel]
  refine ⟨fun ⟨h1, h3⟩ => ⟨by push_cast; omega, ?_⟩, fun ⟨h1, h3⟩ => ?_⟩
  · zify [ht, hs.le.trans ht] at h3
    rw [h1]; linarith
  · have h1 : u s = x := by push_cast at h1; omega
    refine ⟨h1, ?_⟩
    rw [h1] at h3
    zify [ht, hs.le.trans ht]; linarith

theorem Labels.advance {L t t' x : ℕ} {u : ℕ → ℤ} {l : List (ℕ × ℕ)} (h : Labels L u t l) (htt : t < t')
    (hx : u t = x) (hlow : ∀ i, t < i → i < t' → u i ≤ 0) :
    Labels L u t' ((x, area L u t + x * (L - t)) :: l) := by
  intro z y hz
  rw [List.mem_cons, h z y hz, Prod.mk.injEq]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨s, hs, hr⟩)
    exacts [⟨t, htt, hx, rfl⟩, ⟨s, by omega, hr⟩]
  · rintro ⟨s, hs, hr, hy⟩
    rcases lt_trichotomy s t with h' | rfl | h'
    · exact Or.inr ⟨s, h', hr, hy⟩
    · have : z = x := by omega
      exact Or.inl ⟨this, by rw [← hy, this]⟩
    · have := hlow s h' hs; omega

theorem cut_sound {L H t x m n : ℕ} {r : ℕ → ℕ} (hr : ∀ x, Reach x (r x)) (hmono : Monotone r) {u : ℕ → ℤ}
    (hu : Play L u) (hx : u t = x) (hm : ∀ i ≤ t, u i ≤ m) (hn : L ≤ t + n) (h : cut H r n x m = true) :
    ∀ i ≤ L, u i ≤ H := by
  have h : m + r (n - (m - x)) ≤ H := Nat.ble_eq.mp h
  have hxm := hm t le_rfl
  intro i hi
  rcases le_or_gt (t + (m - x)) L with h' | h'
  · obtain ⟨z, hz⟩ := Nat.exists_eq_add_of_le h'
    have hrz : r z ≤ r (n - (m - x)) := hmono (by omega)
    have := (hz ▸ hu : Play (t + (m - x) + z) u).le_of_dip (by omega) hm (by omega) (hr z) i (by omega)
    omega
  · rcases le_total i t with h'' | h''
    · have := hm i h''; omega
    · have := abs_le.mp (le_add_of_step hu.step t (i - t))
      rw [Nat.add_sub_cancel' h''] at this; omega

theorem ok_sound {L L' H : ℕ} {r : ℕ → ℕ} (hr : ∀ x, Reach x (r x)) (hmono : Monotone r) (hL : L' ≤ L)
    {u : ℕ → ℤ} (hu : Play L' u) (h0 : u 0 = 0) : ∀ (f t x m : ℕ) (l : List (ℕ × ℕ)), t ≤ L' → u t = x → 1 ≤ x → (∀ i < t, u i ≤ m) →
      Labels L u t l → ok H r f (L - t) x (area L u t) m l = true → ∀ i ≤ L', u i ≤ H := by
  intro f
  induction f with
  | zero => intro t x m l _ _ _ _ _ h; exact absurd h (by simp [ok])
  | succ f ih =>
    intro t x m l htL hx hx1 hm hl hok
    simp only [ok_succ, node_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq] at hok
    obtain ⟨m', hm'e, hxm, hmm⟩ : ∃ m', (bif Nat.ble m x then x else m) = m' ∧ x ≤ m' ∧ m ≤ m' := by
      refine ⟨_, rfl, ?_⟩
      rcases h : Nat.ble m x with _ | _
      · have : ¬ m ≤ x := by simp [← Nat.ble_eq, h]
        simp; omega
      · have := Nat.ble_eq.mp h; simp; omega
    rw [hm'e] at hok
    have hm' : ∀ i ≤ t, u i ≤ m' := fun i hi => by
      rcases Nat.lt_or_eq_of_le hi with h | rfl
      · have := hm i h; omega
      · omega
    obtain ⟨hmH, hacc | hok⟩ := hok
    · exact cut_sound hr hmono hu hx hm' (by omega) hacc
    -- otherwise the play goes on, if there is time left
    rcases Nat.lt_or_eq_of_le htL with htL | rfl
    swap
    · exact fun i hi => (hm' i hi).trans (by exact_mod_cast hmH)
    have harea : ∀ t' ≤ L', ∀ z : ℕ, t ≤ t' → ∑ i ∈ Ico t t', u i + area L u t = z → area L u t' = z :=
      fun t' ht' z htt hz => by
        have := area_cast hu.step h0 (htL.le.trans hL)
        rw [area, ← sum_range_add_sum_Ico _ htt]; omega
    have next : ∀ x' : ℕ, u (t + 1) = x' → 1 ≤ x' → ok H r f (L - t - 1) x' (area L u t + x) m'
        ((x, area L u t + x * (L - t)) :: l) = true → ∀ i ≤ L', u i ≤ H := fun x' hx' h1 h => by
      refine ih (t + 1) x' m' _ (by omega) hx' h1 (fun i hi => hm' i (by omega))
        (hl.advance (by omega) hx fun i _ _ => by omega) ?_
      rwa [harea (t + 1) (by omega) (area L u t + x) (by omega) (by simp [hx]; ring)]
    have hst := hu.step t
    rcases h2 : Nat.ble 2 x with _ | _ <;> rw [h2] at hok
    · have h1 : x = 1 := by have : ¬ 2 ≤ x := by simp [← Nat.ble_eq, h2]
                            omega
      subst h1
      rw [Bool.cond_false, Bool.and_eq_true] at hok
      rcases hst with e | e
      · exact next 2 (by rw [e, hx]; rfl) (by omega) hok.1
      rcases excursion hu.step (by simpa using hx) (by omega) L' with hlow | ⟨k, j, hk, hret, hlow, hj, hsum⟩
      · intro i hi
        rcases Nat.lt_or_ge t i with h' | h'
        · have := hlow i h' hi; omega
        · exact (hm' i h').trans (by exact_mod_cast hmH)
      · have hmax : ∀ i ≤ t + 2 * k + 2, u i ≤ m' := fun i hi => by
          rcases Nat.lt_or_ge t i with h' | h'
          · rcases Nat.lt_or_eq_of_le hi with hi | rfl
            · have := hlow i h' hi; omega
            · omega
          · exact hm' i h'
        have hL2 : L - (t + 2 * k + 2) = L - t - (k + k + 2) := by omega
        rcases (Bool.or_eq_true _ _).mp (allBelow_spec hok.2 k (by omega)) with hc | hkj
        · exact cut_sound hr hmono hu (by simpa using hret) hmax (by omega) hc
        have hkj := allBelow_spec hkj j (by omega)
        have hA : (k + 2 * j : ℕ) ≤ area L u t + 1 := by
          have := area_cast hu.step h0 (hk.trans hL)
          rw [← sum_range_add_sum_Ico _ (show t ≤ t + 2 * k + 2 by omega), hsum] at this
          have := area_cast hu.step h0 (htL.le.trans hL); omega
        refine ih (t + 2 * k + 2) 1 m' _ hk (by simpa using hret) le_rfl (fun i hi => hmax i hi.le)
          (hl.advance (by omega) hx hlow) ?_
        rw [harea _ hk (area L u t + 1 - (k + (j + j))) (by omega) (by rw [hsum]; omega), hL2]
        exact hkj
    · have h2 := Nat.ble_eq.mp h2
      rw [Bool.cond_true] at hok
      have hw := hl.witness hu.step h0 (htL.le.trans hL) hx h2
      have hrule := hu.rule t htL (by omega)
      rcases hh : hit (x - 1) (area L u t + (x - 1) * (L - t) + 1) l with _ | _ <;> rw [hh] at hok hw
      · have e := hst.resolve_left fun e => by simpa using hw.mpr (hrule.mp e)
        exact next (x - 1) (by omega) (by omega) hok
      · have e := hrule.mpr (hw.mp rfl)
        exact next (x + 1) (by rw [e, hx]; rfl) (by omega) hok

/-- **The search is sound**, for every length up to `L`: a play is free until it first leaves the heights `≤ 0`. -/
theorem reach_of_ok {L H : ℕ} {r : ℕ → ℕ} (hr : ∀ x, Reach x (r x)) (hmono : Monotone r) {f : ℕ}
    (hok : ok H r f (L - 1) 1 (L * L) 0 [] = true) (L' : ℕ) (hL : L' ≤ L) : Reach L' H := by
  intro u hu t ht
  by_contra hc
  classical
  have hex : ∃ i, 1 ≤ u i := ⟨t, by omega⟩
  have hb := Nat.find_spec hex
  have hmin := fun i => Nat.find_min hex (m := i)
  have hbt : Nat.find hex ≤ t := Nat.find_min' hex (by omega)
  obtain ⟨b, hb'⟩ : ∃ b, Nat.find hex = b + 1 :=
    ⟨Nat.find hex - 1, by have : Nat.find hex ≠ 0 := fun h => by have := hu.start; rw [h] at hb; omega
                          omega⟩
  rw [hb'] at hb hbt hmin
  have hlow : ∀ i ≤ b, u i ≤ 0 := fun i hi => by have := hmin i (by omega); omega
  have h0 : u b = 0 := by have := hlow b le_rfl; have := hu.step b; omega
  have h1 : u (b + 1) = 1 := by have := hu.step b; omega
  obtain ⟨z, rfl⟩ := Nat.exists_eq_add_of_le (show b ≤ L' by omega)
  have key := ok_sound (u := fun i => u (b + i) - 0) hr hmono (show z ≤ L by omega) (hu.tail le_rfl hlow)
    (by simp [h0]) f 1 1 0 [] (by omega) (by simp [h1]) le_rfl (fun i hi => by simp [show i = 0 by omega, h0])
    (fun a c ha => by
      simp only [List.not_mem_nil, false_iff]; rintro ⟨s, hs, h, _⟩
      simp [show s = 0 by omega, h0] at h; omega)
    (by have : area L (fun i => u (b + i) - 0) 1 = L * L := by
          simp only [area, range_one, sum_singleton, add_zero, sub_zero, h0, zero_add]
          exact_mod_cast Int.toNat_natCast (L * L)
        rw [this]; simpa using hok) (t - b) (by omega)
  simp only [Nat.add_sub_cancel' (show b ≤ t by omega), sub_zero] at key
  exact hc key

/-! ## The three runs -/

/-- The table after `R 4 ≤ 2` is known, and after `R 13 ≤ 3` is known. -/
def r₄ (x : ℕ) : ℕ := cond (x.ble (nat_lit 1)) x (cond (x.ble (nat_lit 4)) (nat_lit 2) x)
def r₁₃ (x : ℕ) : ℕ := cond (x.ble (nat_lit 4)) (r₄ x) (cond (x.ble (nat_lit 13)) (nat_lit 3) x)

theorem r₄_eq (x : ℕ) : r₄ x = if x ≤ 1 then x else if x ≤ 4 then 2 else x := by
  simp only [r₄, ← Nat.ble_eq, cond_eq_ite]
theorem r₁₃_eq (x : ℕ) : r₁₃ x = if x ≤ 4 then r₄ x else if x ≤ 13 then 3 else x := by
  simp only [r₁₃, ← Nat.ble_eq, cond_eq_ite]

theorem reach_4 : ∀ L ≤ 4, Reach L (2 : ℕ) :=
  reach_of_ok (r := id) reach_self monotone_id (f := 5) (by decide +kernel)

theorem reach_r₄ (x : ℕ) : Reach x (r₄ x) := by
  rw [r₄_eq]; split_ifs with h1 h2
  exacts [reach_self x, reach_4 x h2, reach_self x]

theorem reach_13 : ∀ L ≤ 13, Reach L (3 : ℕ) :=
  reach_of_ok reach_r₄ (fun x y h => by simp only [r₄_eq]; split_ifs <;> omega) (f := 14) (by decide +kernel)

theorem reach_r₁₃ (x : ℕ) : Reach x (r₁₃ x) := by
  rw [r₁₃_eq]; split_ifs with h1 h2
  exacts [reach_r₄ x, reach_13 x h2, reach_self x]

theorem mono_r₁₃ : Monotone r₁₃ := fun x y h => by simp only [r₁₃_eq, r₄_eq]; split_ifs <;> omega

/-- About `80 000` positions; half a minute. -/
theorem reach_28 : ∀ L ≤ 28, Reach L (4 : ℕ) := reach_of_ok reach_r₁₃ mono_r₁₃ (f := 28) (by decide +kernel)

end Recaman
