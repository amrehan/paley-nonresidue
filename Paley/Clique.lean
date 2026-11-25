import Paley.Final

/-!
# Paley graphs

For a prime `p ≡ 1 (mod 4)` the Paley graph on `ZMod p` joins `x ≠ y` when `x - y` is a nonzero square.
Under GRH there are infinitely many primes `p ≡ 1 (mod 8)` whose Paley graph contains a clique of size
`≥ (log p · log log p) / 8`, namely `{0, 1, …, ⌊(log p · log log p) / 8⌋}`.
-/

open Finset Real

namespace Paley

/-- The Paley graph of a prime `p ≡ 1 (mod 4)`. -/
def paleyGraph (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) : SimpleGraph (ZMod p) where
  Adj x y := x ≠ y ∧ IsSquare (x - y)
  symm := ⟨fun x y (h : x ≠ y ∧ IsSquare (x - y)) => by
    refine ⟨h.1.symm, ?_⟩
    have hm1 : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.2 (by omega)
    have := hm1.mul h.2
    rwa [neg_one_mul, neg_sub] at this⟩
  loopless := ⟨fun x (h : x ≠ x ∧ IsSquare (x - x)) => h.1 rfl⟩

theorem paleyGraph_adj {p : ℕ} [Fact p.Prime] {hp : p % 4 = 1} {x y : ZMod p} :
    (paleyGraph p hp).Adj x y ↔ x ≠ y ∧ IsSquare (x - y) := Iff.rfl

/-- The set `{0, 1, …, k}` in `ZMod p` is a clique of the Paley graph when `1, …, k` are squares. -/
theorem isNClique_range (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) (k : ℕ) (hkp : k < p)
    (hsq : ∀ n : ℕ, 0 < n → n ≤ k → IsSquare (n : ZMod p)) :
    (paleyGraph p hp).IsNClique (k + 1) ((range (k + 1)).image (fun i : ℕ => (i : ZMod p))) := by
  have hinj : Set.InjOn (fun i : ℕ => (i : ZMod p)) (range (k + 1) : Set ℕ) := by
    intro i hi j hj h
    simp only [coe_range, Set.mem_Iio] at hi hj
    have := (ZMod.natCast_eq_natCast_iff' i j p).1 h
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  have hm1 : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.2 (by omega)
  refine ⟨?_, by rw [card_image_of_injOn hinj, card_range]⟩
  intro x hx y hy hxy
  simp only [coe_image, coe_range, Set.mem_image, Set.mem_Iio] at hx hy
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj, rfl⟩ := hy
  rw [paleyGraph_adj]
  refine ⟨hxy, ?_⟩
  have hij : i ≠ j := fun h => hxy (by rw [h])
  rcases lt_or_gt_of_ne hij with h | h
  · have hs := hsq (j - i) (by omega) (by omega)
    have := hm1.mul hs
    rw [Nat.cast_sub h.le, neg_one_mul, neg_sub] at this
    exact this
  · have hs := hsq (i - j) (by omega) (by omega)
    rwa [Nat.cast_sub h.le] at hs

/-- **Paley cliques (conditional on GRH).** -/
theorem paley_clique (hGRH : PrimitiveDirichletLZerosOnLine) (X : ℝ) :
    ∃ p : ℕ, ∃ _ : Fact p.Prime, ∃ hp : p % 4 = 1, X < p ∧ p % 8 = 1 ∧
      ∃ k : ℕ, Real.log p * Real.log (Real.log p) / 8 < k ∧
        ∃ S : Finset (ZMod p), (paleyGraph p hp).IsNClique k S := by
  obtain ⟨p, hp, hXp, hp8, hsq⟩ := many_squares hGRH X
  have : Fact p.Prime := ⟨hp⟩
  have hp4 : p % 4 = 1 := by omega
  set x := Real.log p * Real.log (Real.log p) / 8
  set k := ⌊x⌋₊
  have hk : x < k + 1 := Nat.lt_floor_add_one _
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have h1 : Real.log p < p := (Real.log_le_sub_one_of_pos (by linarith)).trans_lt (by linarith)
  have h2 : Real.log (Real.log p) < Real.log p :=
    (Real.log_le_sub_one_of_pos hlp).trans_lt (by linarith)
  have hxp : x < p := by
    rcases le_or_gt (Real.log (Real.log p)) 0 with h | h
    · have : Real.log p * Real.log (Real.log p) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlp.le h
      simp only [x]; linarith
    · have hsqrt := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ p) (by norm_num : (0 : ℝ) < 1 / 2)
      rw [← Real.sqrt_eq_rpow] at hsqrt
      have hs2 : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (by linarith)
      have hl : Real.log p ≤ 2 * Real.sqrt p := by linarith
      have : Real.log p * Real.log (Real.log p) ≤ Real.log p * Real.log p :=
        mul_le_mul_of_nonneg_left h2.le hlp.le
      have : Real.log p * Real.log p ≤ (2 * Real.sqrt p) * (2 * Real.sqrt p) :=
        mul_le_mul hl hl hlp.le (by positivity)
      simp only [x]; nlinarith
  have hkp : k < p := (Nat.floor_lt' hp.ne_zero).2 hxp
  refine ⟨p, inferInstance, hp4, hXp, hp8, k + 1, by push_cast; exact hk, _,
    isNClique_range p hp4 k hkp fun n hn hnk => hsq n hn ?_⟩
  exact (Nat.le_floor_iff' hn.ne').1 hnk

end Paley
