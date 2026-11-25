module

public import Recaman.Growth

/-!
# Growth and balance are the same question

Inverting the master identity gives `β N = a N / N + ∑_{1 ≤ j < N} a j / (j (j + 1))`.  Hence `a N ≤ N β N`, and the
leading constants of `a N / N²` and `β N / N` agree up to a factor `2`.  In particular `a N = o(N²)` iff `β N = o(N)`,
that is, iff the subtractions have frequency `1/2`.
-/

@[expose] public section

namespace Recaman

open Finset Filter Topology

theorem balance_eq {N : ℕ} (hN : 1 ≤ N) :
    (β N : ℝ) = a N / N + ∑ j ∈ Ico 1 N, (a j : ℝ) / (j * (j + 1)) := by
  induction N, hN using Nat.le_induction with
  | base => norm_num [show a 1 = 1 by decide, show β 1 = 1 by decide]
  | succ N hN ih =>
    rw [sum_Ico_succ_top hN]
    have : (0 : ℝ) < N := by exact_mod_cast hN
    rcases step N with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> push_cast <;> rw [ih]
    · rw [h1]; push_cast; field_simp; ring
    · rw [← h1]; push_cast; field_simp; ring

theorem a_le_mul_β (N : ℕ) : (a N : ℝ) ≤ N * β N := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · simp [show a 0 = 0 from rfl]
  have : (0 : ℝ) < N := by exact_mod_cast h
  have hs : 0 ≤ ∑ j ∈ Ico 1 N, (a j : ℝ) / (j * (j + 1)) := sum_nonneg fun j _ => by positivity
  rw [balance_eq h, mul_add, mul_div_cancel₀ _ this.ne']; nlinarith

theorem β_nonneg (N : ℕ) : (0 : ℝ) ≤ β N := by
  rcases Nat.eq_zero_or_pos N with rfl | h
  · simp [β]
  rw [balance_eq h]; have := sum_nonneg fun j (_ : j ∈ Ico 1 N) => (by positivity : 0 ≤ (a j : ℝ) / (j * (j + 1)))
  positivity

/-- A bound on the balance bounds the growth. -/
theorem growth_of_balance {d : ℝ} (h : EvLe (fun N => β N) 1 d) : EvLe (fun N => a N) 2 d := fun ε hε => by
  filter_upwards [h ε hε] with N hN
  have : (0 : ℝ) ≤ N := by positivity
  calc (a N : ℝ) ≤ N * β N := a_le_mul_β N
    _ ≤ N * ((d + ε) * (N : ℝ) ^ 1) := by gcongr
    _ = (d + ε) * N ^ 2 := by ring

/-- A bound on the growth bounds the balance, with twice the constant. -/
theorem balance_of_growth {c : ℝ} (h : EvLe (fun N => a N) 2 c) (hc : 0 ≤ c) :
    EvLe (fun N => β N) 1 (2 * c) := fun ε hε => by
  obtain ⟨N₀, h₀⟩ := eventually_atTop.mp (h (ε / 4) (by positivity))
  set K := ∑ j ∈ Ico 1 (N₀ + 1), (a j : ℝ) / (j * (j + 1))
  filter_upwards [eventually_ge_atTop (N₀ + 1 + ⌈2 * K / ε⌉₊)] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hK : K ≤ ε / 2 * N := by
    have : 2 * K / ε ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast (by omega : ⌈2 * K / ε⌉₊ ≤ N))
    rw [div_le_iff₀ hε] at this; linarith
  have htail : ∑ j ∈ Ico (N₀ + 1) N, (a j : ℝ) / (j * (j + 1)) ≤ (c + ε / 4) * N := by
    calc _ ≤ ∑ _j ∈ Ico (N₀ + 1) N, (c + ε / 4) := sum_le_sum fun j hj => by
          rw [mem_Ico] at hj
          have hj0 : (0 : ℝ) < j := by exact_mod_cast (by omega : 0 < j)
          rw [div_le_iff₀ (by positivity)]
          nlinarith [h₀ j (by omega), (by positivity : 0 ≤ (c + ε / 4) * j)]
      _ ≤ (c + ε / 4) * N := by
          rw [sum_const, Nat.card_Ico, nsmul_eq_mul, mul_comm]
          gcongr; exact_mod_cast Nat.sub_le _ _
  have hlast : (a N : ℝ) / N ≤ (c + ε / 4) * N := by
    rw [div_le_iff₀ hN0]; nlinarith [h₀ N (by omega)]
  rw [balance_eq (by omega), ← sum_Ico_consecutive _ (show 1 ≤ N₀ + 1 by omega) (show N₀ + 1 ≤ N by omega)]
  simp only [pow_one]; linarith

/-- The number of subtractions among the first `N` steps. -/
def S (N : ℕ) : ℕ := #{n ∈ range N | a (n + 1) < a n}

theorem β_eq (N : ℕ) : β N = N - 2 * S N := by
  induction N with
  | zero => simp [β, S]
  | succ N ih =>
    rw [S, range_add_one, filter_insert]
    rcases step N with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2, ih]
    · rw [ite_eq_right (by omega), S]; push_cast; ring
    · rw [ite_eq_left (by omega), card_insert_of_notMem (by simp), S]; push_cast; ring

/-- **`a N = o(N²)` iff the subtractions have frequency `1/2`.** -/
theorem littleO_iff : EvLe (fun N => a N) 2 0 ↔ Tendsto (fun N => (S N : ℝ) / N) atTop (𝓝 (1 / 2)) := by
  have key : EvLe (fun N => a N) 2 0 ↔ EvLe (fun N => β N) 1 0 :=
    ⟨fun h => by simpa using balance_of_growth h le_rfl, growth_of_balance⟩
  have hβ : ∀ N : ℕ, (β N : ℝ) = N - 2 * S N := fun N => by rw [β_eq]; push_cast; ring
  rw [key, Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N₀, h₀⟩ := eventually_atTop.mp (h ε hε)
    refine ⟨N₀ + 1, fun N hN => ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h1 : (β N : ℝ) ≤ ε * N := by simpa using h₀ N (by omega)
    have h2 := β_nonneg N
    rw [hβ] at h1 h2
    rw [Real.dist_eq, abs_lt]
    constructor
    · rw [lt_sub_iff_add_lt, lt_div_iff₀ hN0]; nlinarith
    · rw [sub_lt_iff_lt_add, div_lt_iff₀ hN0]; nlinarith
  · intro h ε hε
    obtain ⟨N₀, h₀⟩ := h (ε / 2) (by positivity)
    filter_upwards [eventually_ge_atTop (N₀ + 1)] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have := (abs_lt.mp (Real.dist_eq _ _ ▸ h₀ N (by omega))).1
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hN0] at this
    simp only [hβ]; nlinarith

end Recaman
