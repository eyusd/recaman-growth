module

public import Recaman.Sequence
public import Recaman.Game

/-!
# Short windows of the sequence are plays

Two terms of indices `k < m` satisfy `a m - a k = m + 1` iff `∑_{k ≤ i < m} (β i - β k) = m (β m - β k - 1) - 1`.
If `m - k` is small against `√m`, the left side is too small for the right side unless `β m - β k = 1`, and then the
condition is `Wit β k m`.  So inside a short window, and above everything visited before it, the rule of the sequence
*is* the rule of the game.
-/

@[expose] public section

namespace Recaman

open Finset

/-- The running maximum. -/
def M (n : ℕ) : ℕ := (range (n + 1)).sup a

theorem a_le_M {k n : ℕ} (h : k ≤ n) : a k ≤ M n := le_sup (f := a) (mem_range.mpr (by omega))

theorem M_le {n B : ℕ} (h : ∀ k ≤ n, a k ≤ B) : M n ≤ B :=
  Finset.sup_le fun k hk => h k (by have := mem_range.mp hk; omega)

/-- Over `t` steps from `n`, the sequence moves by `n` per unit of balance, up to a quadratic error. -/
theorem drift (n t : ℕ) : 2 * |(a (n + t) : ℤ) - a n - n * (β (n + t) - β n)| ≤ t * (t + 1) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have key : |(a (n + (t + 1)) : ℤ) - a n - n * (β (n + (t + 1)) - β n) -
        ((a (n + t) : ℤ) - a n - n * (β (n + t) - β n))| ≤ t + 1 := by
      rw [abs_le]; simp only [← add_assoc]
      rcases step (n + t) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> zify at h1 <;> rw [h2] <;> constructor <;> linarith
    have := abs_sub_abs_le_abs_sub ((a (n + (t + 1)) : ℤ) - a n - n * (β (n + (t + 1)) - β n))
      ((a (n + t) : ℤ) - a n - n * (β (n + t) - β n))
    push_cast at *; nlinarith

/-- The area of a walk over `d` steps is at most `d (d - 1) / 2`. -/
theorem area_bound {u : ℕ → ℤ} (h : ∀ t, u (t + 1) = u t + 1 ∨ u (t + 1) = u t - 1) (s d : ℕ) :
    2 * |∑ i ∈ Ico s (s + d), (u i - u s)| ≤ d * (d - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, sum_Ico_succ_top (by omega)]
    have h1 := abs_add_le (∑ i ∈ Ico s (s + d), (u i - u s)) (u (s + d) - u s)
    have h2 := le_add_of_step h s d
    push_cast; nlinarith

/-- **Locality.** Inside a short window, "the target was visited at time `k`" means "time `k` is a witness". -/
theorem hit_iff_wit {k d : ℕ} (h0 : 0 < d) (hd : d * d < k + d) :
    a k + (k + d + 1) = a (k + d) ↔ Wit β k (k + d) := by
  have key := a_sub_a (Nat.le_add_right k d)
  have hA := area_bound β_step k d
  set A := ∑ i ∈ Ico k (k + d), (β i - β k)
  obtain ⟨hA1, hA2⟩ := abs_le.mp (show |A| ≤ d * d - d by nlinarith [abs_nonneg A])
  zify at h0 hd
  unfold Wit
  rw [show (a k + (k + d + 1) = a (k + d)) ↔ ((a (k + d) : ℤ) - a k = k + d + 1) by omega, key]
  push_cast
  constructor
  · intro h
    have e : (k + d : ℤ) * (β (k + d) - β k - 1) = A + 1 := by linarith
    have h1 : β (k + d) - β k - 1 = 0 := by
      rcases lt_trichotomy (β (k + d) - β k - 1) 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    exact ⟨by linarith, by rw [h1] at e; linarith⟩
  · rintro ⟨h1, h2⟩
    rw [h1, show ∑ i ∈ Ico k (k + d), (β i - β k) = A from rfl] at *
    rw [h2]; ring

/-- **Windows are plays.** After a time `n ≥ (L + 2)²`, lowered by `c` with `M n ≤ a n + c n`, the balance walk is a
play of length `L`. -/
theorem window {L n c : ℕ} (hn : (L + 2) ^ 2 ≤ n) (hc : M n ≤ a n + c * n) :
    Play L (fun t => β (n + t) - (β n + c)) := by
  refine ⟨by simp, fun t => ?_, fun t ht h2 => ?_⟩
  · have := β_step (n + t); simp only [← add_assoc]; omega
  simp only [wit_shift, ← add_assoc]
  rw [show (β (n + t + 1) - (β n + c) = β (n + t) - (β n + c) + 1) ↔ β (n + t + 1) = β (n + t) + 1 by
    constructor <;> intro h <;> linarith]
  -- the target of the step lies above everything visited up to time `n`
  have hfresh : M n + (n + t + 1) < a (n + t) := by
    have hd := (abs_le.mp (by simpa using drift n t :
      |2 * ((a (n + t) : ℤ) - a n - n * (β (n + t) - β n))| ≤ t * (t + 1))).1
    have h3 : (c + 2) * (n : ℤ) ≤ n * (β (n + t) - β n) := by nlinarith
    zify at *; nlinarith
  rw [up_iff (by omega)]
  constructor
  · rintro ⟨k, hk, e⟩
    have hkn : n < k := by by_contra h; have := a_le_M (show k ≤ n by omega); omega
    have hkt : k ≠ n + t := by rintro rfl; omega
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hkn.le
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (show s ≤ t by omega)
    refine ⟨s, by omega, ?_⟩
    rw [← add_assoc n s d] at e ⊢
    exact (hit_iff_wit (by omega) (by nlinarith)).mp (by omega)
  · rintro ⟨s, hs, hw⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs.le
    refine ⟨n + s, by omega, ?_⟩
    rw [← add_assoc n s d] at hw ⊢
    have := (hit_iff_wit (by omega) (by nlinarith)).mpr hw
    omega

/-- **One window** raises the running maximum by at most `(H + 2) n`. -/
theorem M_window {L H n : ℕ} (hR : Reach L H) (hn : (L + 2) ^ 2 ≤ n) : M (n + L) ≤ M n + (H + 2) * n := by
  refine M_le fun k hk => ?_
  rcases le_total k n with h | h
  · exact (a_le_M h).trans (Nat.le_add_right _ _)
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le h
  have hn0 : 0 < n := by nlinarith
  have hM := a_le_M (le_refl n)
  have hc1 := Nat.div_add_mod (M n - a n) n
  have hc2 := Nat.mod_lt (M n - a n) hn0
  set c := (M n - a n) / n
  have := hR _ (window (c := c + 1) hn (by nlinarith [Nat.sub_add_cancel hM])) t (by omega)
  have hd := (abs_le.mp (by simpa using drift n t :
    |2 * ((a (n + t) : ℤ) - a n - n * (β (n + t) - β n))| ≤ t * (t + 1))).2
  have ht : (t : ℤ) ≤ L := by omega
  have hmul : (n : ℤ) * (β (n + t) - β n) ≤ n * (H + c + 1) := by
    push_cast at this; nlinarith
  have hc3 : (n : ℤ) * c ≤ M n - a n := by
    have : n * c ≤ M n - a n := by omega
    zify [hM] at this; exact this
  zify at *; nlinarith

end Recaman
