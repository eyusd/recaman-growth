module

public import Recaman.Search

/-!
# The results

`EvLe f p c` is the statement `limsup f N / N ^ p ≤ c`, in the form: for every `ε > 0`, eventually
`f N ≤ (c + ε) N ^ p`.
-/

@[expose] public section

namespace Recaman

open Filter Topology

/-- **Growth**, from `R 13 ≤ 3`. -/
theorem growth_3_26 : EvLe (fun N => a N) 2 (3 / 26) := by
  convert growth_of_reach (L := 13) (H := 3) (by norm_num) (reach_13 13 le_rfl) using 1; norm_num

/-- **Growth**, from `R 28 ≤ 4`. -/
theorem growth_1_14 : EvLe (fun N => a N) 2 (1 / 14) := by
  convert growth_of_reach (L := 28) (H := 4) (by norm_num) (reach_28 28 le_rfl) using 1; norm_num

/-- At most half of the steps are subtractions. -/
theorem S_le (N : ℕ) : (S N : ℝ) ≤ N / 2 := by
  have h := β_nonneg N
  rw [β_eq] at h; push_cast at h; linarith

/-- A growth constant `c` forces at least `(1/2 - c) N` subtractions. -/
theorem S_ge {c : ℝ} (hc : 0 ≤ c) (h : EvLe (fun N => a N) 2 c) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (1 / 2 - c - ε) * N ≤ S N := fun ε hε => by
  filter_upwards [balance_of_growth h hc (2 * ε) (by positivity)] with N hN
  rw [β_eq] at hN; push_cast at hN; simp only [pow_one] at hN; linarith

theorem S_ge_5_13 : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (5 / 13 - ε) * N ≤ S N := by
  have h := S_ge (by norm_num) growth_3_26
  rwa [show (1 / 2 - 3 / 26 : ℝ) = 5 / 13 by norm_num] at h

theorem S_ge_3_7 : ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, (3 / 7 - ε) * N ≤ S N := by
  have h := S_ge (by norm_num) growth_1_14
  rwa [show (1 / 2 - 1 / 14 : ℝ) = 3 / 7 by norm_num] at h

/-- The dial at `c = 2`, which is a theorem. -/
theorem ρ_le_third : ρ ≤ 1 / 3 := by
  convert ρ_le_of_dial (by norm_num) dial_two using 1; norm_num

/-- The dial at `c = 1`, the witness–descent conjecture, decides the order of growth. -/
theorem of_witness_descent (h : Dial 1) :
    EvLe (fun N => a N) 2 0 ∧ Tendsto (fun N => (S N : ℝ) / N) atTop (𝓝 (1 / 2)) := by
  have : EvLe (fun N => a N) 2 0 := by convert growth_of_dial le_rfl h using 1; norm_num
  exact ⟨this, littleO_iff.mp this⟩

end Recaman
