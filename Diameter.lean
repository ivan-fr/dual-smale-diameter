import DualSmaleGlobal.UnconditionalAndGeometric

open Polynomial Complex
open scoped BigOperators

namespace DualSmaleDiameter
open DualSmaleGlobal

/-- The two paths start at the origin. Together they realize every
distance from a to the interval endpoint ‖b - a‖ inside the sublevel. -/
private theorem sublevel_distance {P : ℂ[X]} {a b : ℂ} {L t : ℝ}
    (hdeg : 1 ≤ P.natDegree) (h0 : P.eval 0 = 0) (hL : 0 < L)
    (hc : ∀ z : ℂ, (derivative P).eval z = 0 → ‖P.eval z‖ < L)
    (ha : ‖P.eval a‖ < L) (hb : ‖P.eval b‖ < L)
    (ht : 0 ≤ t) (htb : t ≤ ‖b - a‖) :
    ∃ z : ℂ, ‖z - a‖ = t ∧ ‖P.eval z‖ < L := by
  by_cases h : t ≤ ‖a‖
  · obtain ⟨g, hg, hg0, hg1, hsub⟩ := sublevel_path_exists P hdeg h0 hL hc ha
    have hcont : ContinuousOn (fun s => ‖g s - a‖) (Set.Icc (0 : ℝ) 1) :=
      (hg.sub continuousOn_const).norm
    have hm : t ∈ Set.Icc ‖g 1 - a‖ ‖g 0 - a‖ := by
      simpa [hg0, hg1] using (show 0 ≤ t ∧ t ≤ ‖a‖ from ⟨ht, h⟩)
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc' zero_le_one hcont hm
    exact ⟨g s, he, hsub s hs⟩
  · obtain ⟨g, hg, hg0, hg1, hsub⟩ := sublevel_path_exists P hdeg h0 hL hc hb
    have hcont : ContinuousOn (fun s => ‖g s - a‖) (Set.Icc (0 : ℝ) 1) :=
      (hg.sub continuousOn_const).norm
    have hm : t ∈ Set.Icc ‖g 0 - a‖ ‖g 1 - a‖ := by
      simpa [hg0, hg1] using (show ‖a‖ ≤ t ∧ t ≤ ‖b - a‖ from ⟨le_of_not_ge h, htb⟩)
    obtain ⟨s, hs, he⟩ := intermediate_value_Icc zero_le_one hcont hm
    exact ⟨g s, he, hsub s hs⟩

/-- Two critical points a and b give a scale-free lower bound using their
chord length. R may be taken to be the largest critical modulus. -/
theorem critical_chord_bound {n : ℕ} (hn : 2 ≤ n) (P : ℂ[X])
    (hdeg : P.natDegree = n) (h0 : P.eval 0 = 0)
    (ζ : Fin (n - 1) → ℂ) (hnz : ∀ k, ζ k ≠ 0)
    (hprod : ∀ z : ℂ, (derivative P).eval z = ∏ k, (1 - z / ζ k))
    {R : ℝ} (hR : ∀ k, ‖ζ k‖ ≤ R) (i j : Fin (n - 1))
    (hij : ζ i ≠ ζ j) :
    ∃ k, 2 * ‖ζ i - ζ j‖ ^ n ≤
      (4 : ℝ)^n * ((n : ℝ) * ∏ l, ‖ζ l‖) * R * ‖P.eval (ζ k) / ζ k‖ := by
  classical
  let D := ‖ζ i - ζ j‖
  have hD : 0 < D := norm_pos_iff.mpr (sub_ne_zero.mpr hij)
  have hne : (Finset.univ : Finset (Fin (n-1))).Nonempty := ⟨i, Finset.mem_univ _⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_mem_eq_sup' hne (fun l => ‖P.eval (ζ l)‖)
  let M := ‖P.eval (ζ k)‖
  have hM : ∀ l, ‖P.eval (ζ l)‖ ≤ M := by
    intro l
    dsimp [M]
    rw [← hk]
    exact Finset.le_sup' (fun s => ‖P.eval (ζ s)‖) (Finset.mem_univ l)
  have hM0 : 0 ≤ M := norm_nonneg _
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hpr : 0 < ∏ l, ‖ζ l‖ := Finset.prod_pos (fun l _ => norm_pos_iff.mpr (hnz l))
  have hlc := norm_leadingCoeff_of_deriv_prod hn P hdeg ζ hnz hprod
  have hcpos : 0 < ‖P.leadingCoeff‖ := by rw [hlc]; positivity
  have hcn := norm_pos_iff.mp hcpos
  have hlim : 2 * D^n / (4 : ℝ)^n * ‖P.leadingCoeff‖ ≤ M := by
    by_contra! hlt
    let L := (M + 2 * D^n / (4 : ℝ)^n * ‖P.leadingCoeff‖) / 2
    have hML : M < L := by dsimp [L]; linarith
    have hc : ∀ z : ℂ, (derivative P).eval z = 0 → ‖P.eval z‖ < L := by
      intro z hz
      rw [hprod, Finset.prod_eq_zero_iff] at hz
      obtain ⟨l, _, he⟩ := hz
      have heq := (div_eq_one_iff_eq (hnz l)).mp (show z / ζ l = 1 by linear_combination -he)
      simpa [heq] using (hM l).trans_lt hML
    have hpick (u : Fin (n+1)) : ∃ z : ℂ,
        ‖z - ζ j‖ = chebNode01 n u * D ∧ ‖P.eval z‖ < L := by
      have hu := chebNode01_mem_Icc (show 1 ≤ n by omega) u
      exact sublevel_distance (by omega) h0 (by linarith) hc
        ((hM j).trans_lt hML) ((hM i).trans_lt hML)
        (mul_nonneg hu.1 hD.le) (by change chebNode01 n u * D ≤ D; nlinarith [hu.2])
    choose z hz hval using hpick
    let Q : ℂ[X] := C (P.leadingCoeff)⁻¹ * P
    have hqd : Q.natDegree = n := by
      dsimp [Q]; rw [natDegree_C_mul (inv_ne_zero hcn), hdeg]
    have hqm : Q.coeff n = 1 := by
      dsimp [Q]; rw [coeff_C_mul, ← hdeg, ← leadingCoeff, inv_mul_cancel₀ hcn]
    have hbound : 2 * D^n / (4 : ℝ)^n ≤ L / ‖P.leadingCoeff‖ := by
      apply monic_chebyshev_continuum_bound (by omega) hqd hqm hD (by positivity) (z := z)
      · intro u v
        have hh := abs_norm_sub_norm_le (z u - ζ j) (z v - ζ j)
        rw [hz u, hz v, ← sub_mul, abs_mul, abs_of_pos hD] at hh
        simpa only [sub_sub_sub_cancel_right] using hh
      · intro u
        dsimp [Q]; rw [eval_mul, eval_C, norm_mul, norm_inv, ← div_eq_inv_mul]
        exact div_le_div_of_nonneg_right (hval u).le hcpos.le
    have hback := (le_div_iff₀ hcpos).mp hbound
    dsimp [L] at hback
    linarith
  refine ⟨k, ?_⟩
  rw [hlc, mul_one_div, div_le_iff₀ (mul_pos hnR hpr), div_le_iff₀ (by positivity)] at hlim
  have hMR : M ≤ R * ‖P.eval (ζ k) / ζ k‖ := by
    rw [norm_div, mul_comm, div_mul_eq_mul_div, le_div_iff₀ (norm_pos_iff.mpr (hnz k))]
    exact mul_le_mul_of_nonneg_left (hR k) hM0
  calc
    2 * D^n ≤ M * ((n : ℝ) * ∏ l, ‖ζ l‖) * 4^n := hlim
    _ ≤ (R * ‖P.eval (ζ k) / ζ k‖) * ((n : ℝ) * ∏ l, ‖ζ l‖) * 4^n := by gcongr
    _ = _ := by ring

/-- Exact conjectured constant whenever the critical chord is long enough. -/
theorem dual_smale_of_critical_chord {n : ℕ} (hn : 2 ≤ n) (P : ℂ[X])
    (hdeg : P.natDegree = n) (h0 : P.eval 0 = 0)
    (ζ : Fin (n - 1) → ℂ) (hnz : ∀ k, ζ k ≠ 0)
    (hprod : ∀ z : ℂ, (derivative P).eval z = ∏ k, (1 - z / ζ k))
    {R : ℝ} (hR : ∀ k, ‖ζ k‖ ≤ R) (i j : Fin (n - 1))
    (hij : ζ i ≠ ζ j)
    (hsize : (4 : ℝ)^n * (∏ l, ‖ζ l‖) * R ≤ 2 * ‖ζ i - ζ j‖^n) :
    ∃ k, 1 / (n : ℝ) ≤ ‖P.eval (ζ k) / ζ k‖ := by
  obtain ⟨k, hk⟩ := critical_chord_bound hn P hdeg h0 ζ hnz hprod hR i j hij
  refine ⟨k, ?_⟩
  have hRpos := (norm_pos_iff.mpr (hnz i)).trans_le (hR i)
  have hpr : 0 < ∏ l, ‖ζ l‖ := Finset.prod_pos (fun l _ => norm_pos_iff.mpr (hnz l))
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hfac : 0 < (4 : ℝ)^n * (∏ l, ‖ζ l‖) * R := by positivity
  rw [div_le_iff₀ hnR]
  apply le_of_mul_le_mul_left (a := (4 : ℝ)^n * (∏ l, ‖ζ l‖) * R) _ hfac
  calc
    _ ≤ 2 * ‖ζ i - ζ j‖^n := by simpa using hsize
    _ ≤ _ := hk
    _ = _ := by ring

end DualSmaleDiameter
#print axioms DualSmaleDiameter.critical_chord_bound
#print axioms DualSmaleDiameter.dual_smale_of_critical_chord
