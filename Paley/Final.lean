import Paley.Main

/-!
# The final asymptotic step

With `y = ⌊log u · log log u / 8⌋`, the hypothesis of `exists_prime` holds for all large `u`. Hence,
under GRH, for every `X` there is a prime `p > X`, `p ≡ 1 (mod 8)`, such that every
`1 ≤ n ≤ (log p · log log p) / 8` is a square modulo `p`.
-/

open Finset Real Filter Asymptotics
open scoped Chebyshev

noncomputable section
namespace Paley

theorem card_oddPrimes_le (y : ℕ) : (oddPrimes y).card ≤ Nat.primeCounting y := by
  rw [Nat.primeCounting_eq_primeCounting'_succ, ← Nat.primesBelow_card_eq_primeCounting']
  refine Finset.card_le_card fun q hq => ?_
  obtain ⟨hqy, hp, -⟩ := mem_oddPrimes.1 hq
  simp only [Nat.primesBelow, mem_filter, mem_range]
  exact ⟨by omega, hp⟩

theorem log_modulus_le (y : ℕ) : Real.log (modulus y) ≤ Real.log 8 + Real.log 4 * y := by
  unfold modulus
  have hpos := prod_oddPrimes_pos y
  rw [Nat.cast_mul, Real.log_mul (by norm_num) (by exact_mod_cast hpos.ne'), Nat.cast_prod,
    Real.log_prod (fun q hq => by exact_mod_cast (mem_oddPrimes.1 hq).2.1.ne_zero)]
  push_cast
  gcongr
  calc ∑ q ∈ oddPrimes y, Real.log q ≤ θ y := by
        unfold Chebyshev.theta
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.log_natCast_nonneg p
        intro q hq
        obtain ⟨hqy, hp, -⟩ := mem_oddPrimes.1 hq
        simp only [mem_filter, mem_Ioc, Nat.floor_natCast]
        exact ⟨⟨hp.pos, hqy⟩, hp⟩
    _ ≤ Real.log 4 * y := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg y)

/-- The purely numerical closing inequality. -/
theorem closing {C u L ℓ q yR nR lM ps : ℝ} (hC : 0 < C) (hu : 900 ≤ u) (hL : L = Real.log u)
    (hL3 : 3 ≤ L) (hℓ17 : 17 ≤ ℓ) (hℓL : ℓ ≤ L) (hq0 : 0 < q) (hq2 : q ^ 2 = Real.sqrt u)
    (hq4 : q ^ 4 = u) (hqexp : q = Real.exp (L / 4))
    (hL2 : L ^ 2 ≤ Real.sqrt u) (hL16 : L ≤ Real.sqrt u / 16) (hK : 32 * (4 * C + 7) * L ^ 4 < q)
    (hn : nR ≤ (Real.log 4 + 1) * L / 8) (hn0 : 0 ≤ nR) (hy : yR ≤ L * ℓ / 8) (hy0 : 0 ≤ yR)
    (hlM : lM ≤ Real.log 8 + Real.log 4 * yR) (hlM0 : 0 ≤ lM)
    (hps : (u - 1) * Real.log 2 - Real.log (u + 2) ≤ ps) :
    Real.exp (nR * Real.log 2) * 8 *
        (C * Real.sqrt u * (lM + L) ^ 2 + lM + 4 * Real.sqrt u * L + Real.log 4 * Real.sqrt u)
      < ps - lM - 2 * Real.sqrt u * L := by
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have hl8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have hsq : 0 < Real.sqrt u := Real.sqrt_pos.2 (by linarith)
  have hsq30 : 30 ≤ Real.sqrt u := by
    rw [show (30 : ℝ) = Real.sqrt 900 by
      rw [show (900 : ℝ) = 30 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hu
  have hsqsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt (by linarith)
  have hl20 : 0 ≤ Real.log 2 := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 ≤ L := by linarith
  -- `2^n ≤ q`
  have h2n : Real.exp (nR * Real.log 2) ≤ q := by
    rw [hqexp]
    refine Real.exp_le_exp.2 ?_
    rw [hl4] at hn
    have a1 : nR * Real.log 2 ≤ (2 * Real.log 2 + 1) * L / 8 * Real.log 2 :=
      mul_le_mul_of_nonneg_right hn hl20
    have a2 : (2 * Real.log 2 + 1) * Real.log 2 ≤ 2 := by nlinarith
    have a3 : (2 * Real.log 2 + 1) * L / 8 * Real.log 2 = (2 * Real.log 2 + 1) * Real.log 2 * L / 8 := by
      ring
    have a4 : (2 * Real.log 2 + 1) * Real.log 2 * L ≤ 2 * L := mul_le_mul_of_nonneg_right a2 hL0
    linarith
  -- `log M ≤ L^2`
  have hlML : lM ≤ L ^ 2 := by
    rw [hl4, hl8] at hlM
    have b1 : yR ≤ L * L / 8 := by
      have := mul_le_mul_of_nonneg_left hℓL hL0
      linarith
    have b2 : 2 * Real.log 2 * yR ≤ 2 * 0.6931471808 * (L * L / 8) :=
      mul_le_mul (by linarith) b1 hy0 (by norm_num)
    have b3 : 9 ≤ L * L := by nlinarith
    have b4 : 3 * Real.log 2 ≤ 3 * 0.6931471808 := by linarith
    have : L ^ 2 = L * L := by ring
    linarith
  have hlog : (lM + L) ^ 2 ≤ 4 * L ^ 4 := by
    have h1 : lM + L ≤ 2 * L ^ 2 := by
      have : L ≤ L ^ 2 := by nlinarith
      linarith
    have h0 : 0 ≤ lM + L := by linarith
    calc (lM + L) ^ 2 ≤ (2 * L ^ 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = 4 * L ^ 4 := by ring
  have hL4 : 1 ≤ L ^ 4 := one_le_pow₀ hL1
  have hLL4 : L ≤ L ^ 4 := by
    calc L = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hL24 : L ^ 2 ≤ L ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hsq1 : 1 ≤ Real.sqrt u := by linarith
  have hlog4 : Real.log 4 ≤ 2 := by rw [hl4]; linarith
  have hlog40 : 0 ≤ Real.log 4 := by rw [hl4]; linarith
  -- bracket ≤ √u (4C+7) L^4
  have hbr : C * Real.sqrt u * (lM + L) ^ 2 + lM + 4 * Real.sqrt u * L + Real.log 4 * Real.sqrt u
      ≤ Real.sqrt u * ((4 * C + 7) * L ^ 4) := by
    have e1 : C * Real.sqrt u * (lM + L) ^ 2 ≤ C * Real.sqrt u * (4 * L ^ 4) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    have e2 : lM ≤ Real.sqrt u * L ^ 4 :=
      hlML.trans (hL24.trans (le_mul_of_one_le_left (by positivity) hsq1))
    have e3 : 4 * Real.sqrt u * L ≤ 4 * Real.sqrt u * L ^ 4 :=
      mul_le_mul_of_nonneg_left hLL4 (by positivity)
    have e4 : Real.log 4 * Real.sqrt u ≤ 2 * Real.sqrt u * L ^ 4 := by
      calc Real.log 4 * Real.sqrt u ≤ 2 * Real.sqrt u := mul_le_mul_of_nonneg_right hlog4 hsq.le
        _ ≤ 2 * Real.sqrt u * L ^ 4 := le_mul_of_one_le_right (by positivity) hL4
    calc _ ≤ C * Real.sqrt u * (4 * L ^ 4) + Real.sqrt u * L ^ 4 + 4 * Real.sqrt u * L ^ 4
          + 2 * Real.sqrt u * L ^ 4 := by linarith
      _ = Real.sqrt u * ((4 * C + 7) * L ^ 4) := by ring
  have hbr0 : 0 ≤ C * Real.sqrt u * (lM + L) ^ 2 + lM + 4 * Real.sqrt u * L
      + Real.log 4 * Real.sqrt u := by positivity
  -- LHS < u / 4
  have hLHS : Real.exp (nR * Real.log 2) * 8 *
        (C * Real.sqrt u * (lM + L) ^ 2 + lM + 4 * Real.sqrt u * L + Real.log 4 * Real.sqrt u)
      < u / 4 := by
    have m1 := mul_le_mul h2n hbr hbr0 hq0.le
    have hK3 : 32 * (4 * C + 7) * L ^ 4 * q ^ 3 < q * q ^ 3 :=
      mul_lt_mul_of_pos_right hK (by positivity)
    calc Real.exp (nR * Real.log 2) * 8 *
          (C * Real.sqrt u * (lM + L) ^ 2 + lM + 4 * Real.sqrt u * L + Real.log 4 * Real.sqrt u)
        = 8 * (Real.exp (nR * Real.log 2) *
          (C * Real.sqrt u * (lM + L) ^ 2 + lM + 4 * Real.sqrt u * L + Real.log 4 * Real.sqrt u)) := by
          ring
      _ ≤ 8 * (q * (Real.sqrt u * ((4 * C + 7) * L ^ 4))) := by linarith
      _ = (32 * (4 * C + 7) * L ^ 4 * q ^ 3) / 4 := by rw [← hq2]; ring
      _ < (q * q ^ 3) / 4 := by linarith
      _ = u / 4 := by rw [← hq4]; ring
  -- RHS ≥ u / 4
  have hlu2 : Real.log (u + 2) ≤ 3 * Real.sqrt u := by
    have : Real.log (u + 2) ≤ Real.log (2 * u) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith), ← hL] at this
    linarith
  have hRHS : u / 4 ≤ ps - lM - 2 * Real.sqrt u * L := by
    have r1 : 2 * Real.sqrt u * L ≤ u / 8 := by
      have := mul_le_mul_of_nonneg_left hL16 (by positivity : (0 : ℝ) ≤ 2 * Real.sqrt u)
      have : 2 * Real.sqrt u * (Real.sqrt u / 16) = Real.sqrt u * Real.sqrt u / 8 := by ring
      linarith
    have r2 : Real.sqrt u * 30 ≤ Real.sqrt u * Real.sqrt u := mul_le_mul_of_nonneg_left hsq30 hsq.le
    have r3 : (u - 1) * 0.6931471803 ≤ (u - 1) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2'.le (by linarith)
    have r4 : lM ≤ Real.sqrt u := hlML.trans hL2
    linarith
  linarith

/-- `y(u) = ⌊log u · log log u / 8⌋`. -/
def yf (u : ℝ) : ℕ := ⌊Real.log u * Real.log (Real.log u) / 8⌋₊

theorem tendsto_yf : Tendsto (fun u => (yf u : ℝ)) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have h1 := Real.tendsto_log_atTop.eventually_ge_atTop (8 * (|b| + 1))
  have h2 := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1
  filter_upwards [h1, h2] with u hu1 hu2
  simp only [Function.comp] at hu2
  have hL : 0 ≤ Real.log u := by have := abs_nonneg b; linarith
  have : Real.log u * 1 ≤ Real.log u * Real.log (Real.log u) := mul_le_mul_of_nonneg_left hu2 hL
  have hfl := Nat.lt_floor_add_one (Real.log u * Real.log (Real.log u) / 8)
  unfold yf
  have := le_abs_self b
  linarith

/-- **Main theorem (conditional on GRH).** For every `X` there is a prime `p > X` with `p ≡ 1 (mod 8)`
such that every `1 ≤ n ≤ (log p · log log p) / 8` is a quadratic residue modulo `p`. -/
theorem many_squares (hGRH : PrimitiveDirichletLZerosOnLine) (X : ℝ) :
    ∃ p : ℕ, p.Prime ∧ X < p ∧ p % 8 = 1 ∧
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.log p * Real.log (Real.log p) / 8 → IsSquare (n : ZMod p) := by
  obtain ⟨C, hC, hex⟩ := exists_prime hGRH
  set K := 4 * C + 7
  have hK0 : 0 < K := by positivity
  have F1 := eventually_ge_atTop (900 : ℝ)
  have F2 := eventually_ge_atTop (max X 0 ^ 2)
  have F3 := (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop (17 : ℝ)
  have F4 := (isLittleO_log_rpow_rpow_atTop 2 (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1)
  have F5 := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by norm_num : (0 : ℝ) < 1 / 16)
  have F6 := (isLittleO_log_rpow_rpow_atTop 4 (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (by positivity : (0 : ℝ) < 1 / (64 * K))
  have F7 := tendsto_yf.eventually (Chebyshev.eventually_primeCounting_le one_pos)
  obtain ⟨u, hu900, huX, hℓ17, h4, h5, h6, h7⟩ := (F1.and (F2.and (F3.and (F4.and (F5.and
    (F6.and F7)))))).exists
  simp only [Function.comp, Nat.floor_natCast] at hℓ17 h7
  set L := Real.log u with hLdef
  set ℓ := Real.log L with hℓdef
  set y := yf u
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hL0 : 0 < L := Real.log_pos (by linarith)
  have hLexp : Real.exp 17 ≤ L := by
    rw [← Real.exp_log hL0]; exact Real.exp_le_exp.2 hℓ17
  have hL18 : 18 ≤ L := by have := Real.add_one_le_exp (17 : ℝ); linarith
  have hL3 : 3 ≤ L := by linarith
  have hℓL : ℓ ≤ L := by have := Real.log_le_sub_one_of_pos hL0; linarith
  have hsqu : Real.sqrt u = u ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow u
  -- the little-o bounds in usable form
  have hL2 : L ^ 2 ≤ Real.sqrt u := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg (by positivity), one_mul, Real.rpow_two] at h4
    rw [hsqu]; exact h4
  have hL16 : L ≤ Real.sqrt u / 16 := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0.le,
      abs_of_nonneg (by positivity)] at h5
    rw [hsqu]; linarith
  set q := u ^ (1 / 4 : ℝ) with hqdef
  have hq0 : 0 < q := Real.rpow_pos_of_pos hu0 _
  have hKq : 32 * K * L ^ 4 < q := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      abs_of_nonneg hq0.le] at h6
    have : L ^ (4 : ℝ) = L ^ 4 := by exact_mod_cast Real.rpow_natCast L 4
    rw [this] at h6
    have h64 : 64 * K * (L ^ 4) ≤ q := by
      have := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤ 64 * K)
      rw [show 64 * K * (1 / (64 * K) * q) = q by field_simp] at this
      linarith
    have : 0 < L ^ 4 := by positivity
    nlinarith
  have hq2 : q ^ 2 = Real.sqrt u := by
    rw [hsqu, hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have hq4 : q ^ 4 = u := by
    rw [hqdef, ← Real.rpow_natCast, ← Real.rpow_mul hu0.le]; norm_num
  have hqexp : q = Real.exp (L / 4) := by
    rw [hqdef, Real.rpow_def_of_pos hu0, hLdef]; ring_nf
  -- `y`
  have hy : (y : ℝ) ≤ L * ℓ / 8 := Nat.floor_le (by positivity)
  have hy1 : L * ℓ / 8 < y + 1 := Nat.lt_floor_add_one _
  have hyL : L ≤ y := by
    have : L * 17 ≤ L * ℓ := mul_le_mul_of_nonneg_left hℓ17 hL0.le
    linarith
  have hlogy : ℓ ≤ Real.log y := Real.log_le_log hL0 hyL
  have hlogy0 : 0 < Real.log y := by linarith
  have hn : ((oddPrimes y).card : ℝ) ≤ (Real.log 4 + 1) * L / 8 := by
    have c1 : ((oddPrimes y).card : ℝ) ≤ Nat.primeCounting y := by
      exact_mod_cast card_oddPrimes_le y
    have c2 : (Real.log 4 + 1) * y / Real.log y ≤ (Real.log 4 + 1) * L / 8 := by
      rw [div_le_iff₀ hlogy0]
      have hl4 : 0 ≤ Real.log 4 + 1 := by
        have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        linarith
      have : (y : ℝ) ≤ L * Real.log y / 8 := by
        have := mul_le_mul_of_nonneg_left hlogy hL0.le
        linarith
      have := mul_le_mul_of_nonneg_left this hl4
      linarith
    linarith
  have hlM := log_modulus_le y
  have hlM0 : 0 ≤ Real.log (modulus y) := Real.log_natCast_nonneg _
  have hps := Chebyshev.psi_ge' hu0.le
  have hcl := closing hC hu900 hLdef hL3 hℓ17 hℓL hq0 hq2 hq4 hqexp hL2 hL16 hKq hn
    (Nat.cast_nonneg _) hy (Nat.cast_nonneg _) hlM hlM0 hps
  -- match the hypothesis of `exists_prime`
  have hpow : (2 : ℝ) ^ ((oddPrimes y).card + 3) = Real.exp ((oddPrimes y).card * Real.log 2) * 8 := by
    rw [Real.exp_nat_mul, Real.exp_log two_pos, pow_add]; norm_num
  have hlogMu : Real.log (modulus y * u) = Real.log (modulus y) + L := by
    rw [Real.log_mul (by exact_mod_cast (modulus_pos y).ne') hu0.ne']
  have hyu : (y : ℝ) < Real.sqrt u := by
    have : L * ℓ / 8 < L ^ 2 := by nlinarith
    linarith
  obtain ⟨p, hp, hpu, hpu', hp8, hsq⟩ := hex y u (by linarith) hyu (by rw [hpow, hlogMu]; exact hcl)
  refine ⟨p, hp, ?_, hp8, fun n hn0 hnp => hsq n hn0 ?_⟩
  · have : max X 0 ≤ Real.sqrt u := by
      rw [← Real.sqrt_sq (le_max_right X 0)]; exact Real.sqrt_le_sqrt huX
    linarith [le_max_left X 0]
  · -- `n ≤ y`
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hlp : 0 < Real.log p := Real.log_pos (by linarith)
    have hlpL : Real.log p ≤ L := Real.log_le_log (by linarith) hpu'
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
    have hll : 0 < Real.log (Real.log p) := by
      by_contra hc
      push_neg at hc
      have : Real.log p * Real.log (Real.log p) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hlp.le hc
      linarith
    have hllℓ : Real.log (Real.log p) ≤ ℓ := Real.log_le_log hlp hlpL
    have : Real.log p * Real.log (Real.log p) ≤ L * ℓ :=
      mul_le_mul hlpL hllℓ hll.le hL0.le
    have : (n : ℝ) ≤ L * ℓ / 8 := by linarith
    exact Nat.le_floor this

end Paley
