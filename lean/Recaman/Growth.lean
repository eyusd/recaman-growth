module

public import Recaman.Window

/-!
# From the reach of the game to the growth of the sequence

`R L` is the reach; it is subadditive, so `R L / L` converges to its infimum `ρ`.  A reach bound for one length
gives `limsup a N / N² ≤ R L / (2 L)` (`growth_of_reach`), hence `limsup a N / N² ≤ ρ / 2` (`growth`).
-/

@[expose] public section

namespace Recaman

open Finset Filter Topology

theorem quadratic {L H : ℕ} (hR : Reach L H) (N : ℕ) :
    2 * L * M N ≤ (H + 2) * N ^ 2 + 2 * L * M ((L + 2) ^ 2 + L) := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rcases Nat.lt_or_ge N ((L + 2) ^ 2 + L) with h | h
    · have : M N ≤ M ((L + 2) ^ 2 + L) := M_le fun k hk => a_le_M (by omega)
      nlinarith [Nat.zero_le ((H + 2) * N ^ 2)]
    · rcases Nat.eq_zero_or_pos L with rfl | hL
      · simp
      obtain ⟨n, rfl⟩ : ∃ n, N = n + L := ⟨N - L, by omega⟩
      have h1 := M_window hR (show (L + 2) ^ 2 ≤ n by omega)
      have h2 := ih n (by omega)
      nlinarith [Nat.zero_le ((H + 2) * L ^ 2)]

/-- A statement of the form `limsup f N / N ^ p ≤ c`. -/
def EvLe (f : ℕ → ℝ) (p : ℕ) (c : ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, f N ≤ (c + ε) * (N : ℝ) ^ p

theorem growth_of_reach {L H : ℕ} (hL : 0 < L) (hR : Reach L H) : EvLe (fun N => a N) 2 (H / (2 * L)) := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / ε)
  have hk0 : (0 : ℝ) < k := lt_trans (by positivity) hk
  have hL0 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hR' : Reach (k * L) ((k * H : ℕ) : ℤ) := by push_cast; exact reach_mul hR k
  set C : ℝ := 2 * (k * L : ℕ) * M ((k * L + 2) ^ 2 + k * L)
  filter_upwards [eventually_ge_atTop (⌈C⌉₊ + 1)] with N hN
  have hC : C ≤ N := (Nat.le_ceil C).trans (by exact_mod_cast (by omega : ⌈C⌉₊ ≤ N))
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hq : 2 * ((k * L : ℕ) : ℝ) * a N ≤ ((k * H : ℕ) + 2) * (N : ℝ) ^ 2 + C := by
    have := (Nat.mul_le_mul_left (2 * (k * L)) (a_le_M le_rfl)).trans (quadratic hR' N)
    simp only [C]; exact_mod_cast this
  have hkε : 2 < ε * k := by rwa [div_lt_iff₀ hε, mul_comm] at hk
  have h3 : C ≤ (N : ℝ) ^ 2 * 1 := by nlinarith
  have h4 : (3 : ℝ) ≤ 2 * k * L * ε := by nlinarith
  have hpos : (0 : ℝ) < 2 * (k * L) := by positivity
  rw [← mul_le_mul_iff_right₀ hpos]
  push_cast at hq
  calc 2 * ((k : ℝ) * L) * a N ≤ (k * H + 2) * N ^ 2 + C := hq
    _ ≤ (k * H + 2 * k * L * ε) * N ^ 2 := by nlinarith
    _ = 2 * (k * L) * ((H / (2 * L) + ε) * N ^ 2) := by field_simp

/-- **The reach** of the game. -/
noncomputable def R (L : ℕ) : ℕ := sInf {H : ℕ | Reach L H}

theorem reach_R (L : ℕ) : Reach L (R L) := Nat.sInf_mem (s := {H : ℕ | Reach L H}) ⟨L, reach_self L⟩

theorem R_le {L H : ℕ} (h : Reach L H) : R L ≤ H := Nat.sInf_le h

theorem R_subadd : Subadditive (fun L => (R L : ℝ)) := fun m n => by
  have : R (m + n) ≤ R m + R n := R_le (by push_cast; exact reach_add (reach_R m) (reach_R n))
  show ((R (m + n) : ℕ) : ℝ) ≤ R m + R n
  exact_mod_cast this

/-- **The reach rate.** -/
noncomputable def ρ : ℝ := R_subadd.lim

theorem bdd : BddBelow (Set.range fun L : ℕ => (R L : ℝ) / L) := ⟨0, by rintro _ ⟨L, rfl⟩; positivity⟩

theorem tendsto_ρ : Tendsto (fun L => (R L : ℝ) / L) atTop (𝓝 ρ) := R_subadd.tendsto_lim bdd

theorem ρ_le {L H : ℕ} (hL : L ≠ 0) (h : Reach L H) : ρ ≤ H / L :=
  (R_subadd.lim_le_div bdd hL).trans (by gcongr; exact R_le h)

theorem ρ_nonneg : 0 ≤ ρ := ge_of_tendsto' tendsto_ρ fun L => by positivity

/-- **Growth.** `limsup a N / N² ≤ ρ / 2`. -/
theorem growth : EvLe (fun N => a N) 2 (ρ / 2) := by
  intro ε hε
  obtain ⟨L, hL, hρ⟩ := ((eventually_gt_atTop 0).and
    (tendsto_ρ.eventually (gt_mem_nhds (show ρ < ρ + ε by linarith)))).exists
  filter_upwards [growth_of_reach hL (reach_R L) (ε / 2) (by positivity)] with N hN
  have : (R L : ℝ) / (2 * L) = R L / L / 2 := by field_simp
  have h2 : (R L : ℝ) / (2 * L) + ε / 2 ≤ ρ / 2 + ε := by linarith
  exact hN.trans (by gcongr)

end Recaman
