module

public import Recaman.Balance

/-!
# The dial

For a `±1` walk `u`, let `W u N` count the up-steps among the first `N` that have a witness, and `D u N` the
down-steps.  `Dial c` says that `W ≤ c · D` for every walk and every `N`.

* `dial_two`: `Dial 2` holds.
* `ρ_le_of_dial`: `Dial c` implies `ρ ≤ (c - 1) / (c + 1)`.
* `growth_of_dial`: hence `limsup a N / N² ≤ (c - 1) / (2 (c + 1))`.

So `Dial 2` gives `ρ ≤ 1/3`, and the conjecture `Dial 1` would give `a N = o(N²)` and the frequency `1/2`.
-/

@[expose] public section

namespace Recaman

open Finset Filter Topology Classical

abbrev Walk (u : ℕ → ℤ) : Prop := ∀ t, u (t + 1) = u t + 1 ∨ u (t + 1) = u t - 1

/-- Witnessed up-steps among the first `N` steps. -/
noncomputable def W (u : ℕ → ℤ) (N : ℕ) : ℕ := #{t ∈ range N | u (t + 1) = u t + 1 ∧ ∃ s < t, Wit u s t}

/-- Down-steps among the first `N` steps. -/
noncomputable def D (u : ℕ → ℤ) (N : ℕ) : ℕ := #{t ∈ range N | u (t + 1) = u t - 1}

def Dial (c : ℝ) : Prop := ∀ u, Walk u → ∀ N, (W u N : ℝ) ≤ c * D u N

/-! ## `Dial 2` -/

/-- A walk that is above `q` at time `s` and at or below `q` at time `t ≥ s` steps down from `q + 1` in between. -/
theorem exists_down {u : ℕ → ℤ} (h : Walk u) {q : ℤ} {s t : ℕ} (hst : s ≤ t) (hs : q < u s) (ht : u t ≤ q) :
    ∃ i, s ≤ i ∧ i < t ∧ u i = q + 1 ∧ u (i + 1) = q := by
  induction t, hst using Nat.le_induction with
  | base => omega
  | succ t hst ih =>
    rcases le_or_gt (u t) q with h' | h'
    · obtain ⟨i, h1, h2, h3⟩ := ih h'; exact ⟨i, h1, by omega, h3⟩
    · have := h t; exact ⟨t, hst, by omega, by omega, by omega⟩

/-- **`W ≤ 2 D`.**  Charge an up-step from height `q` to the last earlier down-step from `q + 1`.  If there is none,
this is the first up-step from `q`; its witness window dips below `q - 1`, so there is a down-step from `q - 1`, to
which it is charged.  Each down-step is charged at most once in each of the two ways. -/
theorem dial_two : Dial 2 := by
  intro u hu N
  set X := {t ∈ range N | u (t + 1) = u t + 1 ∧ ∃ s < t, Wit u s t} with hX
  set Y := {t ∈ range N | u (t + 1) = u t - 1} with hY
  let P : ℕ → ℕ → Prop := fun t i => i < t ∧ u i = u t + 1 ∧ u (i + 1) = u i - 1
  have between : ∀ t₁ ∈ X, ∀ t₂, u t₁ = u t₂ → t₁ < t₂ → ∃ i, t₁ < i ∧ P t₂ i := fun t₁ h₁ t₂ e h => by
    have h₁' : u (t₁ + 1) = u t₁ + 1 := (mem_filter.mp h₁).2.1
    obtain ⟨i, hi1, hi2, hi3, hi4⟩ := exists_down hu (q := u t₂) (show t₁ + 1 ≤ t₂ by omega) (by omega) le_rfl
    exact ⟨i, by omega, hi2, hi3, by omega⟩
  have hA : #{t ∈ X | ∃ i, P t i} ≤ #Y := by
    refine card_le_card_of_injOn (fun t => Nat.findGreatest (P t) t) (fun t ht => ?_) fun t₁ h₁ t₂ h₂ e => ?_
    · obtain ⟨ht, i, hi⟩ := mem_filter.mp ht
      have := Nat.findGreatest_spec (P := P t) hi.1.le hi
      have hN := mem_range.mp (mem_filter.mp ht).1
      exact mem_filter.mpr ⟨mem_range.mpr (this.1.trans hN), this.2.2⟩
    · simp only [coe_filter, Set.mem_ofPred_eq] at h₁ h₂
      obtain ⟨i₁, p₁⟩ := h₁.2; obtain ⟨i₂, p₂⟩ := h₂.2
      have g₁ := Nat.findGreatest_spec (P := P t₁) p₁.1.le p₁
      have g₂ := Nat.findGreatest_spec (P := P t₂) p₂.1.le p₂
      simp only at e
      have hq : u t₁ = u t₂ := by have := g₁.2.1; have := g₂.2.1; rw [e] at *; omega
      rcases lt_trichotomy t₁ t₂ with h | h | h
      · obtain ⟨i, hi, hp⟩ := between t₁ h₁.1 t₂ hq h
        have := Nat.le_findGreatest hp.1.le hp; have := g₁.1; omega
      · exact h
      · obtain ⟨i, hi, hp⟩ := between t₂ h₂.1 t₁ hq.symm h
        have := Nat.le_findGreatest hp.1.le hp; have := g₂.1; omega
  have hB : #{t ∈ X | ¬ ∃ i, P t i} ≤ #Y := by
    have dip : ∀ t ∈ X, ∃ i < t, u i = u t - 1 ∧ u (i + 1) = u i - 1 := fun t ht => by
      obtain ⟨s, hs, h1, h2⟩ := (mem_filter.mp ht).2.2
      obtain ⟨j, hj, hneg⟩ : ∃ j ∈ Ico s t, u j - u s < 0 := by
        by_contra hc; push Not at hc; have := sum_nonneg hc; omega
      rw [mem_Ico] at hj
      obtain ⟨i, hi⟩ := exists_down hu (q := u s - 1) hj.1 (by omega) (by omega)
      exact ⟨i, by omega, by omega, by omega⟩
    choose! f hf using dip
    refine card_le_card_of_injOn f (fun t ht => ?_) fun t₁ h₁ t₂ h₂ e => ?_
    · obtain ⟨ht, _⟩ := mem_filter.mp ht
      have := hf t ht
      exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp (mem_filter.mp ht).1; omega), this.2.2⟩
    · simp only [coe_filter, Set.mem_ofPred_eq] at h₁ h₂
      have hq : u t₁ = u t₂ := by have := (hf t₁ h₁.1).2.1; have := (hf t₂ h₂.1).2.1; rw [e] at *; omega
      rcases lt_trichotomy t₁ t₂ with h | h | h
      · exact absurd ((between t₁ h₁.1 t₂ hq h).imp fun _ => And.right) h₂.2
      · exact h
      · exact absurd ((between t₂ h₂.1 t₁ hq.symm h).imp fun _ => And.right) h₁.2
  have := card_filter_add_card_filter_not (s := X) (fun t => ∃ i, P t i)
  have h : W u N ≤ 2 * D u N := by simp only [W, D, ← hX, ← hY]; omega
  exact_mod_cast h

/-! ## Best plays leave the bottom at once -/

theorem R_affine {ε : ℝ} (hε : 0 < ε) : ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, (R L : ℝ) ≤ (ρ + ε) * L + C := by
  obtain ⟨L₀, h₀⟩ := eventually_atTop.mp (tendsto_ρ.eventually (gt_mem_nhds (show ρ < ρ + ε by linarith)))
  refine ⟨L₀, by positivity, fun L => ?_⟩
  have hq : 0 ≤ (ρ + ε) * L := mul_nonneg (by linarith [ρ_nonneg]) (by positivity)
  rcases Nat.lt_or_ge L (L₀ + 1) with h | h
  · have : R L ≤ L₀ := (R_le (reach_self L)).trans (by omega)
    have : (R L : ℝ) ≤ L₀ := by exact_mod_cast this
    linarith
  · have hL : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    have := h₀ L (by omega)
    rw [div_lt_iff₀ hL] at this
    linarith [(by positivity : (0 : ℝ) ≤ L₀)]

theorem ρ_mul_le (L : ℕ) : ρ * L ≤ R L := by
  rcases Nat.eq_zero_or_pos L with rfl | h
  · simp
  · have := ρ_le h.ne' (reach_R L); rwa [le_div_iff₀ (by exact_mod_cast h)] at this

theorem exists_best {L : ℕ} (h : 0 < R L) : ∃ u, Play L u ∧ ∃ T ≤ L, (R L : ℤ) ≤ u T := by
  by_contra hc
  push Not at hc
  have : Reach L ((R L - 1 : ℕ) : ℤ) := fun u hu t ht => by have := hc u hu t ht; omega
  have := R_le this; omega

/-- **The adversary disappears.**  If `ρ > 0`, a play that reaches `R L` within `L` steps has left the free heights
`≤ 1` for good by a time `o(L)`: coming back to the bottom costs the time of the way down and up again. -/
theorem leaves_bottom (hρ : 0 < ρ) {η : ℝ} (hη : 0 < η) : ∀ᶠ L : ℕ in atTop, ∀ u, Play L u → ∀ T ≤ L,
    (R L : ℤ) ≤ u T → ∃ b ≤ T, (b : ℝ) ≤ η * L ∧ ∀ t, b < t → t ≤ T → 2 ≤ u t := by
  have hρ1 : ρ ≤ 1 := by simpa using ρ_le one_ne_zero (reach_self 1)
  obtain ⟨ε, hε, hε1, hε2⟩ : ∃ ε > 0, ε ≤ ρ ^ 2 / 2 ∧ ε ≤ η * ρ ^ 2 / 2 :=
    ⟨min (ρ ^ 2 / 2) (η * ρ ^ 2 / 2), by positivity, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨C, hC, hR⟩ := R_affine hε
  set K := 4 * C + 8
  filter_upwards [eventually_gt_atTop ⌈K / (ρ ^ 2 / 2)⌉₊, eventually_gt_atTop ⌈K / (η * ρ ^ 2 / 2)⌉₊]
    with L hL1 hL2 u hu T hT hRT
  have hL1 : K < ρ ^ 2 / 2 * L := by
    have := Nat.lt_of_ceil_lt hL1; rwa [div_lt_iff₀ (by positivity), mul_comm] at this
  have hL2 : K < η * ρ ^ 2 / 2 * L := by
    have := Nat.lt_of_ceil_lt hL2; rwa [div_lt_iff₀ (by positivity), mul_comm] at this
  -- `b` is the last time at a height `≤ 1`, and `c` the height reached by then
  set b := Nat.findGreatest (fun t => u t ≤ 1) T
  have hb : u b ≤ 1 := Nat.findGreatest_spec (P := fun t => u t ≤ 1) (Nat.zero_le T) (by have := hu.start; omega)
  have hbT : b ≤ T := Nat.findGreatest_le T
  refine ⟨b, hbT, ?_, fun t h1 h2 => by have := Nat.findGreatest_is_greatest h1 h2; omega⟩
  obtain ⟨s, hs, hmax⟩ := exists_max_image (range (b + 1)) u ⟨0, by simp⟩
  have hsb : s ≤ b := by have := mem_range.mp hs; omega
  obtain ⟨c, hc⟩ : ∃ c : ℕ, (c : ℤ) = max (u s) 0 := ⟨(max (u s) 0).toNat, Int.toNat_of_nonneg (le_max_right _ _)⟩
  have hcR : c ≤ R b := by
    have := reach_R b u (hu.mono (by omega)) s hsb; omega
  have hlow : ∀ t ≤ b, u t ≤ c := fun t ht => by have := hmax t (by simp; omega); omega
  have hup := abs_le.mp (le_add_of_step hu.step b (T - b))
  rw [Nat.add_sub_cancel' hbT] at hup
  have htime : b + R L ≤ L + 1 := by omega
  have hdip : R L ≤ c ∨ b + (c - 1) ≤ L ∧ R L ≤ c + R (L - (b + (c - 1))) := by
    rcases le_or_gt (b + (c - 1)) L with h | h
    · refine Or.inr ⟨h, ?_⟩
      obtain ⟨x, hx⟩ := Nat.exists_eq_add_of_le h
      have := (hx ▸ hu : Play (b + (c - 1) + x) u).le_of_dip (by omega) hlow
        (by have := hlow b le_rfl; omega) (reach_R x) T (by omega)
      rw [show L - (b + (c - 1)) = x by omega]; omega
    · exact Or.inl (by omega)
  have f1 := ρ_mul_le L
  have f2 : (c : ℝ) ≤ (ρ + ε) * b + C := le_trans (by exact_mod_cast hcR) (hR b)
  have f3 : (b : ℝ) + R L ≤ L + 1 := by exact_mod_cast htime
  have hb0 : (0 : ℝ) ≤ b := by positivity
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hεL : ε * L ≤ ρ ^ 2 / 2 * L := by gcongr
  have hεL' : ε * L ≤ η * ρ ^ 2 / 2 * L := by gcongr
  have hε1' : ε ≤ 1 := by nlinarith
  rcases hdip with h | ⟨h1, h2⟩
  · exfalso
    have f5 : (R L : ℝ) ≤ c := by exact_mod_cast h
    have : (ρ + ε) * b ≤ (ρ + ε) * (L + 1 - ρ * L) := by gcongr; linarith
    nlinarith [mul_nonneg (mul_nonneg hε.le hρ.le) hL0]
  · have f5 : (R L : ℝ) ≤ c + R (L - (b + (c - 1))) := by exact_mod_cast h2
    have f6 := hR (L - (b + (c - 1)))
    have f7 : (ρ + ε) * ((L - (b + (c - 1)) : ℕ) : ℝ) ≤ (ρ + ε) * (L - b - c + 1) := by
      rw [Nat.cast_sub h1]; push_cast; gcongr
      have : (c : ℝ) - 1 ≤ ((c - 1 : ℕ) : ℝ) := by
        rw [sub_le_iff_le_add]; exact_mod_cast (by omega : c ≤ c - 1 + 1)
      linarith
    have f8 : ρ * L ≤ c * (1 - (ρ + ε)) + (ρ + ε) * (L - b + 1) + C := by linarith
    have f9 : ρ ^ 2 * b ≤ ε * L + 2 + 2 * C := by
      have hb' := mul_nonneg hε.le hb0
      rcases le_total (ρ + ε) 1 with h | h
      · have : c * (1 - (ρ + ε)) ≤ ((ρ + ε) * b + C) * (1 - (ρ + ε)) := by
          gcongr
        nlinarith [mul_nonneg hb' hρ.le, mul_nonneg hb' hε.le]
      · have : c * (1 - (ρ + ε)) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
        nlinarith [mul_nonneg hb0 hρ.le]
    have hfin : ρ ^ 2 * b ≤ ρ ^ 2 * (η * L) := by linarith
    exact le_of_mul_le_mul_left hfin (by positivity)

/-! ## Turning the dial -/

theorem ups_sub_downs {u : ℕ → ℤ} (h : Walk u) (N : ℕ) :
    u N - u 0 = #{t ∈ range N | u (t + 1) = u t + 1} - (D u N : ℤ) ∧
    #{t ∈ range N | u (t + 1) = u t + 1} + D u N = N := by
  induction N with
  | zero => simp [D]
  | succ N ih =>
    simp only [D, range_add_one, filter_insert] at ih ⊢
    rcases h N with e | e
    · rw [ite_eq_left e, ite_eq_right (by omega), card_insert_of_notMem (by simp)]; push_cast; omega
    · rw [ite_eq_right (by omega), ite_eq_left e, card_insert_of_notMem (by simp)]; push_cast; omega

/-- **The dial.** -/
theorem ρ_le_of_dial {c : ℝ} (hc : 1 ≤ c) (h : Dial c) : ρ ≤ (c - 1) / (c + 1) := by
  rcases ρ_nonneg.eq_or_lt with h0 | hρ
  · rw [← h0]; exact div_nonneg (by linarith) (by linarith)
  rw [le_div_iff₀ (by linarith)]
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hpos : ∀ᶠ L in atTop, 0 < R L := by
    filter_upwards [eventually_gt_atTop 0] with L hL
    have := ρ_mul_le L
    have : (0 : ℝ) < R L := lt_of_lt_of_le (mul_pos hρ (by exact_mod_cast hL)) this
    exact_mod_cast this
  obtain ⟨L, ⟨hlow, hRL⟩, hLδ⟩ := ((leaves_bottom hρ (show 0 < δ / 4 by positivity)).and hpos).and
    (eventually_gt_atTop ⌈4 / δ⌉₊) |>.exists
  have hLδ : 4 < δ * L := by
    have := Nat.lt_of_ceil_lt hLδ; rwa [div_lt_iff₀ hδ, mul_comm] at this
  obtain ⟨u, hu, T, hT, hRT⟩ := exists_best hRL
  obtain ⟨b, hbT, hb, hhigh⟩ := hlow u hu T hT hRT
  obtain ⟨hsub, hadd⟩ := ups_sub_downs hu.step T
  set U := #{t ∈ range T | u (t + 1) = u t + 1}
  -- after time `b` every up-step is witnessed
  have hUW : U ≤ W u T + (b + 1) := by
    have : {t ∈ range T | u (t + 1) = u t + 1} ⊆
        {t ∈ range T | u (t + 1) = u t + 1 ∧ ∃ s < t, Wit u s t} ∪ range (b + 1) := fun t ht => by
      obtain ⟨h1, h2⟩ := mem_filter.mp ht
      have h1 := mem_range.mp h1
      rcases Nat.lt_or_ge t (b + 1) with h' | h'
      · exact mem_union_right _ (mem_range.mpr h')
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_range.mpr h1, h2,
          (hu.rule t (by omega) (hhigh t (by omega) h1.le)).mp h2⟩)
    simpa [W] using (card_le_card this).trans (card_union_le _ _)
  have e1 : (U : ℝ) ≤ W u T + (b + 1) := by exact_mod_cast hUW
  have e2 := h u hu.step T
  have e3 : (R L : ℝ) ≤ U - D u T := by
    have : (R L : ℤ) ≤ U - D u T := by have := hu.start; omega
    exact_mod_cast this
  have e4 : (U : ℝ) + D u T ≤ L := by exact_mod_cast (by omega : U + D u T ≤ L)
  have e5 := ρ_mul_le L
  have hL0 : (0 : ℝ) < L := by by_contra hcon; nlinarith
  have e6 : (c - 1) * (2 * (D u T : ℝ)) ≤ (c - 1) * (L - ρ * L) := by gcongr; linarith
  have : ρ * (c + 1) * L ≤ (c - 1 + δ) * L := by nlinarith
  exact le_of_mul_le_mul_right this hL0

/-- Hence a bound on the growth of the sequence. -/
theorem growth_of_dial {c : ℝ} (hc : 1 ≤ c) (h : Dial c) :
    EvLe (fun N => a N) 2 ((c - 1) / (2 * (c + 1))) := fun ε hε => by
  filter_upwards [growth ε hε] with N hN
  refine hN.trans ?_
  have h1 := ρ_le_of_dial hc h
  have h2 : (c - 1) / (2 * (c + 1)) = (c - 1) / (c + 1) / 2 := by rw [div_div, mul_comm 2]
  rw [h2]; gcongr

end Recaman
