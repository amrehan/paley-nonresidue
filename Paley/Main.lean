import Paley.PsiBound
import Paley.Squares
import Paley.Count

/-!
# Montgomery's argument: a prime that is a square unit modulo `M`

Under GRH, for `M = modulus y` and `u` large in terms of `y`, there is a prime `p ∈ (√u, u]` that is a
square unit modulo `M`; hence `p ≡ 1 (mod 8)` and every `1 ≤ n ≤ y` is a square mod `p`.
-/

open Finset Classical Real ArithmeticFunction
open scoped Chebyshev

noncomputable section
namespace Paley

/-- Contribution of the `n ≤ u` that are not coprime to `M`. -/
def R (M : ℕ) (u : ℝ) : ℝ := ∑ k ∈ Ioc 0 ⌊u⌋₊ with ¬ k.Coprime M, Λ k

theorem Ioc_zero_eq_Icc_one (n : ℕ) : Ioc 0 n = Icc 1 n := by ext; simp; omega

theorem R_nonneg (M : ℕ) (u : ℝ) : 0 ≤ R M u :=
  sum_nonneg fun _ _ => vonMangoldt_nonneg

/-- **Character sums**: every nontrivial `χ` mod `M` has `‖∑_{n≤u} Λ(n) χ(n)‖ ≤ C √u log²(Mu) + R`. -/
theorem psiChar_le (hGRH : PrimitiveDirichletLZerosOnLine) : ∃ C : ℝ, 0 < C ∧
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M), χ ≠ 1 → ∀ u : ℝ, 4 ≤ u →
      ‖∑ k ∈ Ioc 0 ⌊u⌋₊, ((Λ k : ℝ) : ℂ) * χ k‖ ≤ C * Real.sqrt u * Real.log (M * u) ^ 2 + R M u := by
  obtain ⟨C, hC, hpsi⟩ := psi0_le hGRH
  refine ⟨C, hC, fun M _ χ hχ u hu => ?_⟩
  set N := χ.conductor
  haveI : NeZero N := ⟨χ.conductor_ne_zero⟩
  set χs := χ.primitiveCharacter
  have hprim : χs.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hχs : χs ≠ 1 := by
    intro h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter]
    change DirichletCharacter.changeLevel _ χs = 1
    rw [h, DirichletCharacter.changeLevel_one]
  have hNM : (N : ℝ) ≤ M := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) χ.conductor_dvd_level
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have h1 := hpsi N χs hprim u hu
  have hps : Formalism.MainNotions.GlobalTheoryTheory.psi0 χs u = ∑ k ∈ Ioc 0 ⌊u⌋₊, ((Λ k : ℝ) : ℂ) * χs k := by
    unfold Formalism.MainNotions.GlobalTheoryTheory.psi0
    rw [if_neg hχs, sub_zero, Ioc_zero_eq_Icc_one]
  rw [hps] at h1
  have hlog : Real.log (N * u) ^ 2 ≤ Real.log (M * u) ^ 2 := by
    have h0 : 0 ≤ Real.log (N * u) := Real.log_nonneg (by nlinarith)
    have h2 : Real.log (N * u) ≤ Real.log (M * u) :=
      Real.log_le_log (by nlinarith) (by nlinarith)
    exact pow_le_pow_left₀ h0 h2 2
  have h1' : ‖∑ k ∈ Ioc 0 ⌊u⌋₊, ((Λ k : ℝ) : ℂ) * χs k‖ ≤ C * Real.sqrt u * Real.log (M * u) ^ 2 :=
    h1.trans (mul_le_mul_of_nonneg_left hlog (by positivity))
  -- comparison with the primitive character
  have hdiff : ‖∑ k ∈ Ioc 0 ⌊u⌋₊, ((Λ k : ℝ) : ℂ) * χ k - ∑ k ∈ Ioc 0 ⌊u⌋₊, ((Λ k : ℝ) : ℂ) * χs k‖
      ≤ R M u := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans ?_
    unfold R
    rw [Finset.sum_filter]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : k.Coprime M
    · rw [if_neg (not_not.2 hk)]
      have : χ (k : ZMod M) = χs (k : ZMod N) := by
        have hc : IsCoprime (k : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.2 hk
        have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χs χ.conductor_dvd_level hc
        rw [χ.changeLevel_primitiveCharacter] at this
        simpa using this
      rw [this, sub_self, norm_zero]
    · rw [if_pos hk]
      have h0 : χ (k : ZMod M) = 0 :=
        MulChar.map_nonunit _ (by rwa [ZMod.isUnit_iff_coprime])
      rw [h0, mul_zero, zero_sub, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg vonMangoldt_nonneg]
      exact mul_le_of_le_one_right vonMangoldt_nonneg (DirichletCharacter.norm_le_one _ _)
  calc ‖∑ k ∈ Ioc 0 ⌊u⌋₊, ((Λ k : ℝ) : ℂ) * χ k‖
      ≤ ‖∑ k ∈ Ioc 0 ⌊u⌋₊, ((Λ k : ℝ) : ℂ) * χs k‖ +
        ‖∑ k ∈ Ioc 0 ⌊u⌋₊, ((Λ k : ℝ) : ℂ) * χ k - ∑ k ∈ Ioc 0 ⌊u⌋₊, ((Λ k : ℝ) : ℂ) * χs k‖ :=
        norm_le_insert' _ _
    _ ≤ _ := by linarith

/-- `R ≤ log M + 2 √u log u`. -/
theorem R_le (M : ℕ) [NeZero M] {u : ℝ} (hu : 1 ≤ u) :
    R M u ≤ Real.log M + 2 * Real.sqrt u * Real.log u := by
  have hM0 : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  unfold R
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun k => k.Prime)]
  rw [Finset.filter_filter, Finset.filter_filter]
  gcongr
  · -- primes dividing `M`
    calc ∑ k ∈ Ioc 0 ⌊u⌋₊ with ¬k.Coprime M ∧ k.Prime, Λ k
        = ∑ k ∈ Ioc 0 ⌊u⌋₊ with ¬k.Coprime M ∧ k.Prime, Real.log k := by
          refine Finset.sum_congr rfl fun k hk => ?_
          exact vonMangoldt_apply_prime (mem_filter.1 hk).2.2
      _ ≤ ∑ p ∈ M.primeFactors, Real.log p := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ =>
            Real.log_natCast_nonneg p
          intro k hk
          simp only [mem_filter] at hk
          obtain ⟨-, hcop, hp⟩ := hk
          rw [Nat.mem_primeFactors]
          exact ⟨hp, (Nat.Prime.dvd_iff_not_coprime hp).2 hcop, NeZero.ne M⟩
      _ ≤ Real.log M := by
          rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero),
            ← Nat.cast_prod]
          have hpos : 0 < ∏ p ∈ M.primeFactors, p :=
            Finset.prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
          refine Real.log_le_log (by exact_mod_cast hpos) ?_
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (Nat.prod_primeFactors_dvd M)
  · -- non-primes
    calc ∑ k ∈ Ioc 0 ⌊u⌋₊ with ¬k.Coprime M ∧ ¬k.Prime, Λ k
        ≤ ∑ k ∈ Ioc 0 ⌊u⌋₊ with ¬k.Prime, Λ k := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => vonMangoldt_nonneg
          intro k; simp only [mem_filter]; tauto
      _ = ψ u - θ u := (Chebyshev.psi_sub_theta_eq_sum_not_prime u).symm
      _ ≤ 2 * Real.sqrt u * Real.log u := Chebyshev.psi_sub_theta_le hu

/-- The trivial character mod `M` sees exactly the `n` coprime to `M`. -/
theorem psi_one (M : ℕ) [NeZero M] (u : ℝ) :
    ∑ k ∈ Ioc 0 ⌊u⌋₊, Λ k * ((1 : DirichletCharacter ℂ M) k).re = ψ u - R M u := by
  unfold R Chebyshev.psi
  rw [← Finset.sum_filter_add_sum_filter_not (Ioc 0 ⌊u⌋₊) (fun k => k.Coprime M) (fun k => Λ k),
    ← Finset.sum_filter_add_sum_filter_not (Ioc 0 ⌊u⌋₊) (fun k => k.Coprime M)]
  have h1 : ∀ k ∈ (Ioc 0 ⌊u⌋₊).filter (fun k => k.Coprime M),
      Λ k * ((1 : DirichletCharacter ℂ M) k).re = Λ k := by
    intro k hk
    have hu : IsUnit (k : ZMod M) := (ZMod.isUnit_iff_coprime k M).2 (mem_filter.1 hk).2
    rw [MulChar.one_apply hu, Complex.one_re, mul_one]
  have h2 : ∀ k ∈ (Ioc 0 ⌊u⌋₊).filter (fun k => ¬ k.Coprime M),
      Λ k * ((1 : DirichletCharacter ℂ M) k).re = 0 := by
    intro k hk
    have hu : ¬ IsUnit (k : ZMod M) := by
      rw [ZMod.isUnit_iff_coprime]; exact (mem_filter.1 hk).2
    rw [MulChar.map_nonunit _ hu, Complex.zero_re, mul_zero]
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_const_zero]
  ring

/-- If no prime in `(√u, u]` is a square unit mod `M`, the weighted count is small. -/
theorem SH_le (M : ℕ) [NeZero M] {u : ℝ} (hu : 1 ≤ u)
    (hno : ∀ p : ℕ, p.Prime → Real.sqrt u < p → (p : ℝ) ≤ u → indH M p = 0) :
    ∑ k ∈ Ioc 0 ⌊u⌋₊, Λ k * indH M k ≤ Real.log 4 * Real.sqrt u + 2 * Real.sqrt u * Real.log u := by
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun k => k.Prime)]
  gcongr
  · calc ∑ k ∈ Ioc 0 ⌊u⌋₊ with k.Prime, Λ k * indH M k
        ≤ ∑ k ∈ Ioc 0 ⌊u⌋₊ with k.Prime, (if (k : ℝ) ≤ Real.sqrt u then Real.log k else 0) := by
          refine Finset.sum_le_sum fun k hk => ?_
          obtain ⟨hk1, hp⟩ := mem_filter.1 hk
          rw [vonMangoldt_apply_prime hp]
          split_ifs with h
          · exact mul_le_of_le_one_right (Real.log_natCast_nonneg k) (indH_le_one _)
          · have hku : (k : ℝ) ≤ u := by
              have := (mem_Ioc.1 hk1).2
              exact (Nat.cast_le.2 this).trans (Nat.floor_le (by linarith))
            rw [hno k hp (not_le.1 h) hku, mul_zero]
      _ = ∑ k ∈ (Ioc 0 ⌊u⌋₊).filter (fun k : ℕ => k.Prime ∧ (k : ℝ) ≤ Real.sqrt u), Real.log (k : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.filter_filter]
      _ ≤ θ (Real.sqrt u) := by
          unfold Chebyshev.theta
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => Real.log_natCast_nonneg p
          intro k hk
          simp only [mem_filter, mem_Ioc] at hk ⊢
          refine ⟨⟨hk.1.1, Nat.le_floor hk.2.2⟩, hk.2.1⟩
      _ ≤ Real.log 4 * Real.sqrt u := Chebyshev.theta_le_log4_mul_x (Real.sqrt_nonneg u)
  · calc ∑ k ∈ Ioc 0 ⌊u⌋₊ with ¬k.Prime, Λ k * indH M k
        ≤ ∑ k ∈ Ioc 0 ⌊u⌋₊ with ¬k.Prime, Λ k :=
          Finset.sum_le_sum fun k _ => mul_le_of_le_one_right vonMangoldt_nonneg (indH_le_one _)
      _ = ψ u - θ u := (Chebyshev.psi_sub_theta_eq_sum_not_prime u).symm
      _ ≤ 2 * Real.sqrt u * Real.log u := Chebyshev.psi_sub_theta_le hu

/-- **Existence of a prime that is a square unit mod `M`** (Montgomery's argument, under GRH). -/
theorem exists_prime (hGRH : PrimitiveDirichletLZerosOnLine) : ∃ C : ℝ, 0 < C ∧
    ∀ (y : ℕ) (u : ℝ), 4 ≤ u → (y : ℝ) < Real.sqrt u →
      (2 : ℝ) ^ ((oddPrimes y).card + 3) *
          (C * Real.sqrt u * Real.log (modulus y * u) ^ 2 + Real.log (modulus y)
            + 4 * Real.sqrt u * Real.log u + Real.log 4 * Real.sqrt u)
        < ψ u - Real.log (modulus y) - 2 * Real.sqrt u * Real.log u →
      ∃ p : ℕ, p.Prime ∧ Real.sqrt u < p ∧ (p : ℝ) ≤ u ∧ p % 8 = 1 ∧
        ∀ n : ℕ, 0 < n → n ≤ y → IsSquare (n : ZMod p) := by
  obtain ⟨C, hC, hchar⟩ := psiChar_le hGRH
  refine ⟨C, hC, fun y u hu hyu hbig => ?_⟩
  set M := modulus y
  by_contra hne
  have hno : ∀ p : ℕ, p.Prime → Real.sqrt u < p → (p : ℝ) ≤ u → indH M p = 0 := by
    intro p hp hpu hpu'
    unfold indH
    split_ifs with hb
    · exfalso
      have hyp : y < p := by exact_mod_cast hyu.trans hpu
      obtain ⟨h8, hsq⟩ := isSquare_of_sq_mod hp hyp hb
      exact hne ⟨p, hp, hpu, hpu', h8, hsq⟩
    · rfl
  have hu1 : (1 : ℝ) ≤ u := by linarith
  set B := C * Real.sqrt u * Real.log (M * u) ^ 2 + R M u
  have hB0 : 0 ≤ B := by
    have := R_nonneg M u; positivity
  have hcount := count_ge (M := M) (Ioc 0 ⌊u⌋₊) (fun k => Λ k) B hB0
    (fun χ hχ => hchar M χ hχ u hu)
  rw [psi_one] at hcount
  have hS := SH_le M hu1 hno
  have hR := R_le M hu1
  set H := Nat.card (sqSub M)
  set K := Nat.card (powMonoidHom 2 : (ZMod M)ˣ →* (ZMod M)ˣ).ker
  have hφ : (M.totient : ℝ) = K * H := by
    have := card_units_eq y; exact_mod_cast this
  have hH : (0 : ℝ) < H := by
    have : 0 < H := Nat.card_pos
    exact_mod_cast this
  have hK : (K : ℝ) ≤ 2 ^ ((oddPrimes y).card + 3) := by
    exact_mod_cast card_ker_sq_le y
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  -- `H (ψ - R) ≤ φ (B + S)` with `S` the bound of `SH_le`
  set S := Real.log 4 * Real.sqrt u + 2 * Real.sqrt u * Real.log u
  have hS0 : 0 ≤ S := by
    have : 0 ≤ Real.log u := Real.log_nonneg hu1
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have h1 : (H : ℝ) * (ψ u - R M u) ≤ K * H * (B + S) := by
    have := mul_le_mul_of_nonneg_left hS (Nat.cast_nonneg M.totient)
    rw [hφ] at hcount this
    nlinarith
  have h2 : ψ u - R M u ≤ K * (B + S) := by
    have : (H : ℝ) * (ψ u - R M u) ≤ H * (K * (B + S)) := by linarith
    exact le_of_mul_le_mul_left this hH
  have h3 : K * (B + S) ≤ 2 ^ ((oddPrimes y).card + 3) * (B + S) :=
    mul_le_mul_of_nonneg_right hK (by linarith)
  have h4 : B + S ≤ C * Real.sqrt u * Real.log (M * u) ^ 2 + Real.log M
      + 4 * Real.sqrt u * Real.log u + Real.log 4 * Real.sqrt u := by
    simp only [B, S]; linarith
  have h5 := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 2 ^ ((oddPrimes y).card + 3))
  linarith

end Paley
