module

public import Mathlib.Tactic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Subadditive

/-!
# Recamán's sequence and its balance walk

`a 0 = 0`, and `a (n+1) = a n - (n+1)` if that is non-negative and new, else `a n + (n+1)`.

The **balance** `β n` is the number of additions minus the number of subtractions among the first `n` steps.
It is a `±1` walk, and the sequence is recovered from it by one identity (`a_sub_a`): for `k ≤ m`

  `a m - a k = m (β m - β k) - ∑_{k ≤ i < m} (β i - β k)`.

Everything else in this development reads the sequence through this identity.
-/

@[expose] public section

namespace Recaman

open Finset

/-- The terms `a n, …, a 0`, most recent first. -/
def terms : ℕ → List ℕ
  | 0 => [0]
  | n + 1 =>
    let l := terms n
    let p := l.headD 0
    (if n + 1 ≤ p ∧ p - (n + 1) ∉ l then p - (n + 1) else p + (n + 1)) :: l

/-- Recamán's sequence, OEIS A005132. -/
def a (n : ℕ) : ℕ := (terms n).headD 0

example : (List.range 24).map a =
    [0, 1, 3, 6, 2, 7, 13, 20, 12, 21, 11, 22, 10, 23, 9, 24, 8, 25, 43, 62, 42, 63, 41, 18] := by
  decide +kernel

theorem mem_terms {v n : ℕ} : v ∈ terms n ↔ ∃ k ≤ n, a k = v := by
  induction n with
  | zero => simp [terms, a, eq_comm]
  | succ n ih =>
    have h : terms (n + 1) = a (n + 1) :: terms n := rfl
    rw [h, List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨k, hk, rfl⟩)
      exacts [⟨n + 1, le_rfl, rfl⟩, ⟨k, by omega, rfl⟩]
    · rintro ⟨k, hk, rfl⟩
      rcases Nat.lt_or_eq_of_le hk with h | rfl
      exacts [Or.inr ⟨k, by omega, rfl⟩, Or.inl rfl]

/-- **The recurrence.** Step `n+1` subtracts if its target is non-negative and new, and adds otherwise. -/
theorem recurrence (n : ℕ) :
    (a (n + 1) + (n + 1) = a n ∧ ∀ k ≤ n, a k + (n + 1) ≠ a n) ∨
    (a (n + 1) = a n + (n + 1) ∧ (n + 1 ≤ a n → ∃ k ≤ n, a k + (n + 1) = a n)) := by
  have h : a (n + 1) = if n + 1 ≤ a n ∧ a n - (n + 1) ∉ terms n then a n - (n + 1) else a n + (n + 1) := rfl
  split_ifs at h with hc
  · obtain ⟨h1, h2⟩ := hc
    exact Or.inl ⟨by omega, fun k hk e => h2 (mem_terms.mpr ⟨k, hk, by omega⟩)⟩
  · refine Or.inr ⟨h, fun h1 => ?_⟩
    obtain ⟨k, hk, e⟩ := mem_terms.mp (not_not.mp fun h2 => hc ⟨h1, h2⟩)
    exact ⟨k, hk, by omega⟩

/-- Additions minus subtractions among the first `n` steps. -/
def β : ℕ → ℤ
  | 0 => 0
  | n + 1 => β n + if a n < a (n + 1) then 1 else -1

/-- A step is an addition or a subtraction, and `β` records which. -/
theorem step (n : ℕ) : (a (n + 1) = a n + (n + 1) ∧ β (n + 1) = β n + 1) ∨
    (a (n + 1) + (n + 1) = a n ∧ β (n + 1) = β n - 1) := by
  rcases recurrence n with ⟨h, _⟩ | ⟨h, _⟩
  · right; simp [β, h, show ¬ a n < a (n + 1) by omega, sub_eq_add_neg]
  · left; simp [β, h]

theorem β_step (n : ℕ) : β (n + 1) = β n + 1 ∨ β (n + 1) = β n - 1 := (step n).imp And.right And.right

/-- A step whose target is non-negative is an addition iff the target has been visited. -/
theorem up_iff {n : ℕ} (h : n + 1 ≤ a n) : β (n + 1) = β n + 1 ↔ ∃ k ≤ n, a k + (n + 1) = a n := by
  rcases recurrence n with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases step n with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> try omega
  · exact iff_of_false (by omega) (by push Not; exact h2)
  · exact iff_of_true h4 (h2 h)

/-- **The master identity.** -/
theorem a_sub_a {k m : ℕ} (h : k ≤ m) :
    (a m : ℤ) - a k = m * (β m - β k) - ∑ i ∈ Ico k m, (β i - β k) := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m hkm ih =>
    rw [sum_Ico_succ_top hkm]
    rcases step m with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> zify at h1 <;> rw [h2] <;> push_cast <;> linarith

end Recaman
