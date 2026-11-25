import Main
import Paley

/-!
# Unconditional results

Alpöge's `LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine` (from `src/Main.lean` of
his archive) discharges the GRH hypothesis of `Paley.many_squares` and `Paley.paley_clique`.

Unconditionally, there are infinitely many primes `p` (all `≡ 1 mod 8`) such that every
`1 ≤ n ≤ (log p · log log p) / 8` is a quadratic residue mod `p`. Equivalently, the least quadratic
non-residue satisfies `n₂(p) > (log p · log log p) / 8` infinitely often, and the Paley graph of `p`
has a clique of size `> (log p · log log p) / 8`. (Montgomery 1971 under GRH; previously the best
unconditional bound was `≫ log p · log log log p`, Graham–Ringrose 1990.)
-/

open Real

namespace Paley

/-- **Unconditional.** For every `X` there is a prime `p > X`, `p ≡ 1 (mod 8)`, such that every
`1 ≤ n ≤ (log p · log log p) / 8` is a square modulo `p`. -/
theorem many_squares_unconditional (X : ℝ) :
    ∃ p : ℕ, p.Prime ∧ X < p ∧ p % 8 = 1 ∧
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.log p * Real.log (Real.log p) / 8 → IsSquare (n : ZMod p) :=
  many_squares LFunction_eq_zero_re_of_isPrimitive X

/-- **Unconditional.** Infinitely many primes have all of `1, …, ⌊(log p · log log p)/8⌋` as squares. -/
theorem infinite_primes_many_squares :
    {p : ℕ | p.Prime ∧ p % 8 = 1 ∧
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.log p * Real.log (Real.log p) / 8 → IsSquare (n : ZMod p)}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨p, hp, hap, hp8, hsq⟩ := many_squares_unconditional a
  exact ⟨p, ⟨hp, hp8, hsq⟩, by exact_mod_cast hap⟩

/-- **Unconditional, least quadratic non-residue.** For infinitely many primes `p`, every quadratic
non-residue `n` mod `p` satisfies `n > (log p · log log p) / 8`. -/
theorem least_nonresidue_large :
    {p : ℕ | p.Prime ∧ ∀ n : ℕ, ¬ IsSquare (n : ZMod p) →
      Real.log p * Real.log (Real.log p) / 8 < n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt fun a => ?_
  obtain ⟨p, hp, hap, -, hsq⟩ := many_squares_unconditional a
  refine ⟨p, ⟨hp, fun n hn => ?_⟩, by exact_mod_cast hap⟩
  by_contra h
  push_neg at h
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · exact hn ⟨0, by simp⟩
  · exact hn (hsq n hn0 h)

/-- **Unconditional, Paley graphs.** For every `X` there is a prime `p > X`, `p ≡ 1 (mod 8)`, whose
Paley graph contains a clique with more than `(log p · log log p) / 8` vertices. -/
theorem paley_clique_unconditional (X : ℝ) :
    ∃ p : ℕ, ∃ _ : Fact p.Prime, ∃ hp : p % 4 = 1, X < p ∧ p % 8 = 1 ∧
      ∃ k : ℕ, Real.log p * Real.log (Real.log p) / 8 < k ∧
        ∃ S : Finset (ZMod p), (paleyGraph p hp).IsNClique k S :=
  paley_clique LFunction_eq_zero_re_of_isPrimitive X

end Paley


#print axioms Paley.many_squares_unconditional
#print axioms Paley.infinite_primes_many_squares
#print axioms Paley.least_nonresidue_large
#print axioms Paley.paley_clique_unconditional
