import Mathlib
import Statements
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitFormulaClosed
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroCountHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PsiChiSqrtLogBound

/-!
# Square-root bound for `ψ(u, χ)` under GRH, uniform in the modulus

Under GRH for primitive Dirichlet characters, `‖ψ₀(u, χ)‖ ≤ C √u log² (N u)` for every primitive
`χ` mod `N` and every `u ≥ 4`, where `ψ₀(u, χ) = ∑_{n ≤ u} Λ(n) χ(n) - [χ = 1] u`.
All analytic input (truncated explicit formula, zero counting) is taken from Alpöge's archive.
-/

open Finset ArithmeticFunction GlobalTheory.Mem.An Formalism.MainNotions

noncomputable section
namespace Paley

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

theorem inv_norm_le_two (hGRH : PrimitiveDirichletLZerosOnLine) (hχ : χ.IsPrimitive) {ρ : ℂ}
    {t T : ℝ} (hρ : ρ ∈ zerosIn χ t T) : 1 / ‖ρ‖ ≤ 2 := by
  obtain ⟨h0, h1, -, hL⟩ := hρ
  have hre : ρ.re = 1 / 2 := hGRH q χ hχ ρ h0 h1 hL
  have h4 : 1 / 2 ≤ ‖ρ‖ := hre ▸ Complex.re_le_norm ρ
  rw [div_le_iff₀ (by linarith)]
  linarith

theorem zsumR_inv_norm_one_le (hGRH : PrimitiveDirichletLZerosOnLine) (hχ : χ.IsPrimitive) :
    zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) ≤ 2 * zsumR χ 0 1 (fun _ => 1) := by
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  rw [zsumR_eq_sum_toFinset χ 0 1 _ hf, zsumR_eq_sum_toFinset χ 0 1 _ hf, Finset.mul_sum]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have := mul_le_mul_of_nonneg_left (inv_norm_le_two hGRH hχ (by simpa using hρ))
    (Nat.cast_nonneg (α := ℝ) (zmult χ ρ))
  linarith

theorem zsumR_inv_norm_le (hGRH : PrimitiveDirichletLZerosOnLine) (hχ : χ.IsPrimitive) (T : ℝ) :
    zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) ≤ 2 * zsumR χ 0 1 (fun _ => 1) +
      zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) := by
  classical
  have hf := (ZeroWindow.finite_and_one_le_zmult q χ 0 T).1
  have hf1 := (ZeroWindow.finite_and_one_le_zmult q χ 0 1).1
  have h1 := sum_indicator_le_zsumR χ 0 1 hf.toFinset hf1
  rw [zsumR_eq_sum_toFinset χ 0 T _ hf, zsumR_eq_sum_toFinset χ 0 T _ hf]
  refine le_trans ?_ (add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) le_rfl)
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ρ hρ => ?_
  have hρ' : ρ ∈ zerosIn χ 0 T := by simpa using hρ
  have hm : (0 : ℝ) ≤ zmult χ ρ := Nat.cast_nonneg _
  by_cases h : 1 < |ρ.im|
  · rw [if_pos h]
    split_ifs <;> linarith
  · have h2 : ρ ∈ zerosIn χ 0 1 := ⟨hρ'.1, hρ'.2.1, by rw [sub_zero]; linarith, hρ'.2.2.2⟩
    rw [if_neg h, if_pos h2]
    have := mul_le_mul_of_nonneg_left (inv_norm_le_two hGRH hχ h2) hm
    linarith

theorem norm_cpow_zero_le (hGRH : PrimitiveDirichletLZerosOnLine) (hχ : χ.IsPrimitive)
    {u : ℝ} (hu : 0 < u) {T : ℝ} : ∀ ρ ∈ zerosIn χ 0 T, ‖(u : ℂ) ^ ρ‖ ≤ Real.sqrt u := by
  rintro ρ ⟨h0, h1, -, hL⟩
  have hre : ρ.re = 1 / 2 := hGRH q χ hχ ρ h0 h1 hL
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, hre, Real.sqrt_eq_rpow]

/-- **GRH square-root bound**, uniform in the modulus. -/
theorem psi0_le (hGRH : PrimitiveDirichletLZerosOnLine) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u : ℝ, 4 ≤ u →
      ‖GlobalTheoryTheory.psi0 χ u‖ ≤ C * Real.sqrt u * Real.log (N * u) ^ 2 := by
  obtain ⟨A, hA⟩ := GlobalTheory.ExplicitFormulaClosed.explicit_formula_closed
  obtain ⟨B, hB⟩ := zsumR_recip_le zeroCount_holds
  refine ⟨|A| * 10 + |B| * 10 + |A| * |B| * 10 + 1, by positivity, fun N _ χ hχ u hu => ?_⟩
  set T := Real.sqrt u with hT
  have hT2 : 2 ≤ T := by
    rw [hT, show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hu
  have hTu : T ≤ u := by
    rw [hT, Real.sqrt_le_left (by linarith)]; nlinarith
  have hu0 : 0 < u := by linarith
  have hTT : T * T = u := Real.mul_self_sqrt hu0.le
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  -- logs
  set L := Real.log (N * u) with hL
  have hNu : 4 ≤ (N : ℝ) * u := by nlinarith
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hTNu : T ≤ N * u := by nlinarith
  have hlogNuT : Real.log (N * u * T) ≤ 2 * L := by
    rw [hL, ← Real.log_rpow (by linarith), Real.log_le_log_iff (by positivity) (by positivity)]
    rw [Real.rpow_two]; nlinarith [mul_le_mul_of_nonneg_left hTNu (by linarith : (0:ℝ) ≤ N * u)]
  have hlogNuT0 : 0 ≤ Real.log (N * u * T) :=
    Real.log_nonneg (by nlinarith)
  have hlog3N : Real.log (3 * N) ≤ 2 * L := by
    rw [hL, ← Real.log_rpow (by linarith), Real.log_le_log_iff (by positivity) (by positivity)]
    rw [Real.rpow_two]; nlinarith
  have hlogNT : Real.log (N * T) ≤ L := by
    rw [hL, Real.log_le_log_iff (by positivity) (by positivity)]; nlinarith
  have hlogNT0 : 0 ≤ Real.log (N * T) := Real.log_nonneg (by nlinarith)
  -- pieces
  have e1 := hA N χ hχ u T hT2 hTu
  obtain ⟨hB1, hB2⟩ := hB N χ hχ T hT2
  have z1 := zsumR_inv_norm_one_le hGRH hχ
  have z2 := zsumR_inv_norm_le hGRH hχ T
  have hz := GlobalTheory.Mem.An.GoodLarge.norm_zsum_le χ u T (Real.sqrt u) (norm_cpow_zero_le hGRH hχ hu0)
  have hsq0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
  have hZ0 : 0 ≤ zsumR χ 0 1 (fun _ => 1) := by
    unfold zsumR
    exact finsum_nonneg fun _ => finsum_nonneg fun _ => by simp
  have hpsi : ‖GlobalTheoryTheory.psi0 χ u‖ ≤
      ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ +
        ‖zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ := by
    have := norm_sub_le (GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ))
      (zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ))
    simpa using this
  -- u log²/T = √u log²
  have huT : u * Real.log (N * u * T) ^ 2 / T = T * Real.log (N * u * T) ^ 2 := by
    rw [← hTT]; field_simp
  rw [huT] at e1
  have hlogNu : Real.log (N * u) = L := rfl
  -- bound everything by multiples of T * L^2
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hT0 : 0 ≤ T := by linarith
  have hTL : T ≤ T * L ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left hL2 hT0]
  have hLL2 : L ≤ L ^ 2 := by nlinarith
  have hLL : L ≤ T * L ^ 2 := by nlinarith
  have hTL1 : T * L ≤ T * L ^ 2 := mul_le_mul_of_nonneg_left hLL2 hT0
  have hsqL : Real.log (N * u * T) ^ 2 ≤ 4 * L ^ 2 :=
    (pow_le_pow_left₀ hlogNuT0 hlogNuT 2).trans_eq (by ring)
  have hsqL' : Real.log (N * T) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hlogNT0 hlogNT 2
  have hl3 : 0 ≤ Real.log (3 * N) := Real.log_nonneg (by linarith)
  have hzs1 : zsumR χ 0 1 (fun _ => 1) ≤ |B| * (2 * L) :=
    hB2.trans ((mul_le_mul_of_nonneg_right (le_abs_self B) hl3).trans
      (mul_le_mul_of_nonneg_left hlog3N (abs_nonneg B)))
  have hzsT : zsumR χ 0 T (fun ρ => if 1 < |ρ.im| then 1 / ‖ρ‖ else 0) ≤ |B| * L ^ 2 :=
    hB1.trans ((mul_le_mul_of_nonneg_right (le_abs_self B) (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hsqL' (abs_nonneg B)))
  have hzsR0 : 0 ≤ zsumR χ 0 T (fun ρ => 1 / ‖ρ‖) := by
    unfold zsumR
    exact finsum_nonneg fun _ => finsum_nonneg fun _ => by positivity
  have hzsR1 : 0 ≤ zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖) := by
    unfold zsumR
    exact finsum_nonneg fun _ => finsum_nonneg fun _ => by positivity
  have hE : ‖GlobalTheoryTheory.psi0 χ u + zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤
      |A| * (T * (4 * L ^ 2) + L + 2 * (|B| * (2 * L))) := by
    refine e1.trans ?_
    have : T * Real.log (N * u * T) ^ 2 + Real.log (N * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)
        ≤ T * (4 * L ^ 2) + L + 2 * (|B| * (2 * L)) := by
      have := mul_le_mul_of_nonneg_left hsqL (by linarith : (0 : ℝ) ≤ T)
      linarith
    calc A * (T * Real.log (N * u * T) ^ 2 + Real.log (N * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖))
        ≤ |A| * (T * Real.log (N * u * T) ^ 2 + Real.log (N * u) + zsumR χ 0 1 (fun ρ => 1 / ‖ρ‖)) :=
          mul_le_mul_of_nonneg_right (le_abs_self A) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left this (abs_nonneg A)
  have hZ : ‖zsum χ 0 T (fun ρ => (u : ℂ) ^ ρ / ρ)‖ ≤ T * (2 * (|B| * (2 * L)) + |B| * L ^ 2) := by
    refine hz.trans (mul_le_mul_of_nonneg_left ?_ hsq0)
    linarith
  have hB0 := abs_nonneg B
  have hA0 := abs_nonneg A
  have k1 : |A| * L ≤ |A| * (T * L ^ 2) := mul_le_mul_of_nonneg_left hLL hA0
  have k2 : |A| * |B| * L ≤ |A| * |B| * (T * L ^ 2) :=
    mul_le_mul_of_nonneg_left hLL (mul_nonneg hA0 hB0)
  have k3 : |B| * (T * L) ≤ |B| * (T * L ^ 2) := mul_le_mul_of_nonneg_left hTL1 hB0
  have k4 : 0 ≤ |A| * (T * L ^ 2) := mul_nonneg hA0 (by positivity)
  have k5 : 0 ≤ |B| * (T * L ^ 2) := mul_nonneg hB0 (by positivity)
  have k6 : 0 ≤ |A| * |B| * (T * L ^ 2) := mul_nonneg (mul_nonneg hA0 hB0) (by positivity)
  have k7 : 0 ≤ T * L ^ 2 := by positivity
  calc ‖GlobalTheoryTheory.psi0 χ u‖ ≤ _ := hpsi
    _ ≤ |A| * (T * (4 * L ^ 2) + L + 2 * (|B| * (2 * L))) +
          T * (2 * (|B| * (2 * L)) + |B| * L ^ 2) := add_le_add hE hZ
    _ = 4 * (|A| * (T * L ^ 2)) + |A| * L + 4 * (|A| * |B| * L) + 4 * (|B| * (T * L))
          + |B| * (T * L ^ 2) := by ring
    _ ≤ (|A| * 10 + |B| * 10 + |A| * |B| * 10 + 1) * T * L ^ 2 := by
      have : (|A| * 10 + |B| * 10 + |A| * |B| * 10 + 1) * T * L ^ 2
          = 10 * (|A| * (T * L ^ 2)) + 10 * (|B| * (T * L ^ 2)) + 10 * (|A| * |B| * (T * L ^ 2))
            + T * L ^ 2 := by ring
      rw [this]; linarith

end Paley
