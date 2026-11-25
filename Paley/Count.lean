import Mathlib

/-!
# Counting in the subgroup of squares via character orthogonality

For a modulus `M`, let `H ≤ (ZMod M)ˣ` be the subgroup of squares, `1_H` its indicator on `ZMod M`
and `c χ = ∑_{a ∈ H} χ(a⁻¹)`. Then `φ(M) 1_H(k) = ∑_χ c χ · χ(k)`, each `c χ ∈ {0, |H|}`,
`∑_χ c χ = φ(M)`, and consequently, for any weights `w ≥ 0`, if every nontrivial character sum
`∑ w(k) χ(k)` has norm `≤ B`, then `φ(M) ∑ w(k) 1_H(k) ≥ |H| ∑ w(k) 1(k) - φ(M) B`.
-/

open Finset Classical

noncomputable section
namespace Paley

variable {M : ℕ} [NeZero M]

/-- The subgroup of squares. -/
abbrev sqSub (M : ℕ) : Subgroup (ZMod M)ˣ := (powMonoidHom 2 : (ZMod M)ˣ →* (ZMod M)ˣ).range

/-- Indicator of being a square unit. -/
def indH (M : ℕ) (k : ZMod M) : ℝ :=
  if ∃ b : (ZMod M)ˣ, ((b ^ 2 : (ZMod M)ˣ) : ZMod M) = k then 1 else 0

theorem indH_nonneg (k : ZMod M) : 0 ≤ indH M k := by unfold indH; split_ifs <;> norm_num

theorem indH_le_one (k : ZMod M) : indH M k ≤ 1 := by unfold indH; split_ifs <;> norm_num

/-- `c χ = ∑_{a ∈ H} χ(a⁻¹)`. -/
def cH (χ : DirichletCharacter ℂ M) : ℂ := ∑ a : sqSub M, χ (((a : (ZMod M)ˣ)⁻¹ : (ZMod M)ˣ) : ZMod M)

theorem orth (k : ZMod M) :
    ((M.totient : ℂ)) * (indH M k : ℂ) = ∑ χ : DirichletCharacter ℂ M, cH χ * χ k := by
  simp only [cH, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [← map_mul, DirichletCharacter.sum_characters_eq]
  by_cases hk : ∃ b : (ZMod M)ˣ, ((b ^ 2 : (ZMod M)ˣ) : ZMod M) = k
  · obtain ⟨b, hb⟩ := hk
    have hind : indH M k = 1 := by unfold indH; rw [if_pos ⟨b, hb⟩]
    rw [hind]
    let a0 : sqSub M := ⟨b ^ 2, b, rfl⟩
    have : ∀ a : sqSub M, ((((a : (ZMod M)ˣ)⁻¹ : (ZMod M)ˣ) : ZMod M) * k = 1 ↔ a = a0) := by
      intro a
      constructor
      · intro h
        apply Subtype.ext
        apply Units.ext
        rw [← hb] at h
        have := congrArg (fun z => ((a : (ZMod M)ˣ) : ZMod M) * z) h
        simp only [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul,
          mul_one] at this
        exact this.symm
      · rintro rfl
        rw [← hb, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true, Complex.ofReal_one, mul_one]
  · have hind : indH M k = 0 := by unfold indH; rw [if_neg hk]
    rw [hind]
    simp only [Complex.ofReal_zero, mul_zero]
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [if_neg]
    intro h
    apply hk
    obtain ⟨b, hb⟩ := (a : sqSub M).2
    refine ⟨b, ?_⟩
    have := congrArg (fun z => ((a : (ZMod M)ˣ) : ZMod M) * z) h
    simp only [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul,
      mul_one] at this
    rw [this]
    simp only [powMonoidHom_apply] at hb
    rw [hb]

theorem cH_cases (χ : DirichletCharacter ℂ M) :
    cH χ = 0 ∨ cH χ = (Nat.card (sqSub M) : ℂ) := by
  by_cases h : ∀ a : sqSub M, χ ((a : (ZMod M)ˣ) : ZMod M) = 1
  · right
    unfold cH
    have : ∀ a : sqSub M, χ (((a : (ZMod M)ˣ)⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := by
      intro a
      have := h a⁻¹
      simpa using this
    simp [this, Nat.card_eq_fintype_card]
  · left
    push_neg at h
    obtain ⟨h0, hh⟩ := h
    have key : χ ((h0 : (ZMod M)ˣ) : ZMod M) * cH χ = cH χ := by
      unfold cH
      rw [Finset.mul_sum]
      refine Fintype.sum_equiv (Equiv.mulRight h0⁻¹) _ _ fun a => ?_
      simp only [Equiv.coe_mulRight, Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv,
        Units.val_mul, map_mul]
    have : (χ ((h0 : (ZMod M)ˣ) : ZMod M) - 1) * cH χ = 0 := by rw [sub_mul, key]; ring
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd (sub_eq_zero.1 h1) hh
    · exact h1

theorem sum_cH : ∑ χ : DirichletCharacter ℂ M, cH χ = (M.totient : ℂ) := by
  have := orth (M := M) 1
  have hind : indH M 1 = 1 := by unfold indH; rw [if_pos ⟨1, by simp⟩]
  rw [hind] at this
  simpa using this.symm

theorem cH_one : cH (1 : DirichletCharacter ℂ M) = (Nat.card (sqSub M) : ℂ) := by
  unfold cH
  simp [Nat.card_eq_fintype_card]

theorem cH_re_nonneg (χ : DirichletCharacter ℂ M) : cH χ = ((cH χ).re : ℂ) ∧ 0 ≤ (cH χ).re := by
  rcases cH_cases χ with h | h <;> rw [h] <;> simp

/-- **Main counting inequality.** -/
theorem count_ge (s : Finset ℕ) (w : ℕ → ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ χ : DirichletCharacter ℂ M, χ ≠ 1 → ‖∑ k ∈ s, (w k : ℂ) * χ k‖ ≤ B) :
    (Nat.card (sqSub M) : ℝ) * ∑ k ∈ s, w k * ((1 : DirichletCharacter ℂ M) k).re
      - M.totient * B ≤ M.totient * ∑ k ∈ s, w k * indH M k := by
  -- complex identity
  have hid : ((M.totient : ℂ)) * ∑ k ∈ s, (w k : ℂ) * (indH M k : ℂ)
      = ∑ χ : DirichletCharacter ℂ M, cH χ * ∑ k ∈ s, (w k : ℂ) * χ k := by
    calc ((M.totient : ℂ)) * ∑ k ∈ s, (w k : ℂ) * (indH M k : ℂ)
        = ∑ k ∈ s, (w k : ℂ) * (((M.totient : ℂ)) * (indH M k : ℂ)) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ k ∈ s, (w k : ℂ) * ∑ χ : DirichletCharacter ℂ M, cH χ * χ k := by
          exact Finset.sum_congr rfl fun k _ => by rw [orth]
      _ = ∑ χ : DirichletCharacter ℂ M, cH χ * ∑ k ∈ s, (w k : ℂ) * χ k := by
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun k _ => by ring
  have hre := congrArg Complex.re hid
  have hL : (((M.totient : ℂ)) * ∑ k ∈ s, (w k : ℂ) * (indH M k : ℂ)).re
      = M.totient * ∑ k ∈ s, w k * indH M k := by
    rw [show ((M.totient : ℂ)) * ∑ k ∈ s, (w k : ℂ) * (indH M k : ℂ)
      = ((M.totient * ∑ k ∈ s, w k * indH M k : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]
  rw [hL, Complex.re_sum] at hre
  rw [hre, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1)]
  -- trivial character term
  have h1 : (cH (1 : DirichletCharacter ℂ M) * ∑ k ∈ s, (w k : ℂ) * (1 : DirichletCharacter ℂ M) k).re
      = (Nat.card (sqSub M) : ℝ) * ∑ k ∈ s, w k * ((1 : DirichletCharacter ℂ M) k).re := by
    rw [cH_one, ← Complex.ofReal_natCast, Complex.re_ofReal_mul, Complex.re_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.re_ofReal_mul]
  rw [h1]
  -- the others
  have h2 : ∀ χ ∈ (univ : Finset (DirichletCharacter ℂ M)).erase 1,
      -((cH χ).re * B) ≤ (cH χ * ∑ k ∈ s, (w k : ℂ) * χ k).re := by
    intro χ hχ
    have hne : χ ≠ 1 := Finset.ne_of_mem_erase hχ
    obtain ⟨hc, hc0⟩ := cH_re_nonneg χ
    set r := (cH χ).re
    rw [hc, Complex.re_ofReal_mul]
    have h6 := (Complex.abs_re_le_norm (∑ k ∈ s, (w k : ℂ) * χ k)).trans (hB χ hne)
    have h7 := (abs_le.1 h6).1
    have := mul_le_mul_of_nonneg_left h7 hc0
    linarith
  have h3 : ∑ χ ∈ (univ : Finset (DirichletCharacter ℂ M)).erase 1, (cH χ).re ≤ M.totient := by
    have := congrArg Complex.re (sum_cH (M := M))
    rw [Complex.re_sum, Complex.natCast_re, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1),
      cH_one, Complex.natCast_re] at this
    have : (0 : ℝ) ≤ Nat.card (sqSub M) := Nat.cast_nonneg _
    linarith
  have h4 := Finset.sum_le_sum h2
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul] at h4
  have h5 : (∑ χ ∈ (univ : Finset (DirichletCharacter ℂ M)).erase 1, (cH χ).re) * B
      ≤ M.totient * B := mul_le_mul_of_nonneg_right h3 hB0
  linarith

end Paley
