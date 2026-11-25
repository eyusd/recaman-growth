module

public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Subadditive

/-!
# The window game

A **play** of length `L` is a `±1` walk `u` on `ℤ` with `u 0 ≤ 0`.  Below height `2` its steps are free.  At height
`≥ 2` they are forced: the walk steps up iff some earlier time `s` **witnesses** the step, meaning that the walk
stood one lower at time `s`, and its mean height over `(s, t]` is exactly that height.

`Reach L H` says that no play of length `L` gets above height `H`.  The rule only mentions height differences over a
stretch of time, so it is invariant under shifts in time and height; hence the reach is subadditive (`reach_add`).
-/

@[expose] public section

namespace Recaman

open Finset

/-- The walk stood one lower at `s`, and `∑_{s ≤ i < t} (u i - u s) = -1`. -/
def Wit (u : ℕ → ℤ) (s t : ℕ) : Prop := u t = u s + 1 ∧ ∑ i ∈ Ico s t, (u i - u s) = -1

structure Play (L : ℕ) (u : ℕ → ℤ) : Prop where
  start : u 0 ≤ 0
  step : ∀ t, u (t + 1) = u t + 1 ∨ u (t + 1) = u t - 1
  rule : ∀ t < L, 2 ≤ u t → (u (t + 1) = u t + 1 ↔ ∃ s < t, Wit u s t)

def Reach (L : ℕ) (H : ℤ) : Prop := ∀ u, Play L u → ∀ t ≤ L, u t ≤ H

theorem Play.mono {L L' : ℕ} {u : ℕ → ℤ} (h : Play L u) (hL : L' ≤ L) : Play L' u :=
  ⟨h.start, h.step, fun t ht => h.rule t (by omega)⟩

/-- Witnesses are invariant under shifts of time and height. -/
theorem wit_shift (u : ℕ → ℤ) (b : ℕ) (c : ℤ) (s t : ℕ) :
    Wit (fun i => u (b + i) - c) s t ↔ Wit u (b + s) (b + t) := by
  have e : ∑ i ∈ Ico s t, (u (b + i) - c - (u (b + s) - c)) = ∑ i ∈ Ico (b + s) (b + t), (u i - u (b + s)) := by
    rw [add_comm b s, add_comm b t, ← sum_Ico_add (fun i => u i - u (s + b)) s t b]
    simp only [sub_sub_sub_cancel_right]
  unfold Wit
  rw [← e]
  exact and_congr (by constructor <;> intro h <;> linarith) Iff.rfl

/-- **Tails.** If a play stays at or below `c ≥ 0` up to time `b`, then what follows, lowered by `c`, is a play: a
witness of a step from height `≥ c + 2` stands above `c`, hence after time `b`. -/
theorem Play.tail {L b : ℕ} {c : ℤ} {u : ℕ → ℤ} (h : Play (b + L) u) (hc : 0 ≤ c) (hb : ∀ t ≤ b, u t ≤ c) :
    Play L (fun i => u (b + i) - c) := by
  refine ⟨by simpa using hb b le_rfl, fun t => ?_, fun t ht h2 => ?_⟩
  · have := h.step (b + t)
    simp only [← add_assoc]; omega
  · have h2' : 2 ≤ u (b + t) := by omega
    have := h.rule (b + t) (by omega) h2'
    simp only [← add_assoc, wit_shift]
    rw [show (u (b + t + 1) - c = u (b + t) - c + 1) ↔ u (b + t + 1) = u (b + t) + 1 by
      constructor <;> intro h <;> linarith, this]
    constructor
    · rintro ⟨s, hs, hw⟩
      have : b < s := by
        by_contra hsb
        have := hb s (by omega); have := hw.1; omega
      exact ⟨s - b, by omega, by rwa [show b + (s - b) = s by omega]⟩
    · rintro ⟨s, hs, hw⟩
      exact ⟨b + s, by omega, hw⟩

theorem le_add_of_step {u : ℕ → ℤ} (h : ∀ t, u (t + 1) = u t + 1 ∨ u (t + 1) = u t - 1) (s d : ℕ) :
    |u (s + d) - u s| ≤ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [abs_le] at ih ⊢
    have := h (s + d); rw [add_assoc] at this
    push_cast; omega

theorem reach_self (L : ℕ) : Reach L L := fun u h t ht => by
  have := abs_le.mp (le_add_of_step h.step 0 t)
  have := h.start; simp at *; omega

theorem Reach.mono {L : ℕ} {H H' : ℤ} (h : Reach L H) (hH : H ≤ H') : Reach L H' :=
  fun u hu t ht => (h u hu t ht).trans hH

/-- The walk that always steps down is a play, so a reach bound is non-negative. -/
theorem Reach.nonneg {L : ℕ} {H : ℤ} (h : Reach L H) : 0 ≤ H :=
  h (fun t => -t) ⟨by simp, fun t => by push_cast; omega, fun t _ h => by omega⟩ 0 (by omega)

/-- **The dip bound.** A play that has stayed at or below `c` up to time `b`, and stands at `c - d` then, is at most
`c + H` afterwards if `Reach (L - d) H`: it needs `d` steps to come back to height `c`. -/
theorem Play.le_of_dip {L b d : ℕ} {c H : ℤ} {u : ℕ → ℤ} (h : Play (b + d + L) u) (hc : 0 ≤ c)
    (hb : ∀ t ≤ b, u t ≤ c) (hd : u b + d ≤ c) (hR : Reach L H) : ∀ t ≤ b + d + L, u t ≤ c + H := by
  have hlow : ∀ t ≤ b + d, u t ≤ c := fun t ht => by
    rcases le_total t b with h' | h'
    · exact hb t h'
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
      have := abs_le.mp (le_add_of_step h.step b j); omega
  intro t ht
  rcases le_total t (b + d) with h' | h'
  · have := hlow t h'; have := hR.nonneg; omega
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le h'
    have := hR _ (h.tail hc hlow) j (by omega)
    simp at this; omega

/-- **Subadditivity.** -/
theorem reach_add {L₁ L₂ : ℕ} {H₁ H₂ : ℤ} (h₁ : Reach L₁ H₁) (h₂ : Reach L₂ H₂) : Reach (L₁ + L₂) (H₁ + H₂) :=
  fun u hu => Play.le_of_dip (d := 0) (by simpa using hu) h₁.nonneg (h₁ u (hu.mono (by omega)))
    (by simpa using h₁ u (hu.mono (by omega)) L₁ le_rfl) h₂

theorem reach_mul {L : ℕ} {H : ℤ} (h : Reach L H) : ∀ k : ℕ, Reach (k * L) (k * H)
  | 0 => by simpa using reach_self 0
  | k + 1 => by
    have := reach_add (reach_mul h k) h
    rw [show (k + 1) * L = k * L + L by ring]; push_cast
    rwa [show ((k : ℤ) + 1) * H = k * H + H by ring]

end Recaman
