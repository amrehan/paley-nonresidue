# Statements

These are the exact Lean statements, in namespace `Paley`. Each conditional theorem takes
`hGRH : PrimitiveDirichletLZerosOnLine` as its first argument; `Unconditional/Unconditional.lean` restates the main
ones without it. Every theorem below has `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

## The hypothesis (Alpöge's `src/Statements.lean`)

GRH for primitive Dirichlet L-functions, used verbatim from Alpöge's archive:

```lean
def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2
```

His `src/Main.lean` proves `theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine`.

## Unconditional results (`Unconditional/Unconditional.lean`)

```lean
theorem Paley.many_squares_unconditional (X : ℝ) :
    ∃ p : ℕ, p.Prime ∧ X < p ∧ p % 8 = 1 ∧
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.log p * Real.log (Real.log p) / 8 → IsSquare (n : ZMod p)

theorem Paley.infinite_primes_many_squares :
    {p : ℕ | p.Prime ∧ p % 8 = 1 ∧
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.log p * Real.log (Real.log p) / 8 → IsSquare (n : ZMod p)}.Infinite

theorem Paley.least_nonresidue_large :
    {p : ℕ | p.Prime ∧ ∀ n : ℕ, ¬ IsSquare (n : ZMod p) →
      Real.log p * Real.log (Real.log p) / 8 < n}.Infinite

theorem Paley.paley_clique_unconditional (X : ℝ) :
    ∃ p : ℕ, ∃ _ : Fact p.Prime, ∃ hp : p % 4 = 1, X < p ∧ p % 8 = 1 ∧
      ∃ k : ℕ, Real.log p * Real.log (Real.log p) / 8 < k ∧
        ∃ S : Finset (ZMod p), (paleyGraph p hp).IsNClique k S
```

## Paley graphs (`Paley/Clique.lean`)

```lean
/-- The Paley graph of a prime `p ≡ 1 (mod 4)`. -/
def paleyGraph (p : ℕ) [Fact p.Prime] (hp : p % 4 = 1) : SimpleGraph (ZMod p) where
  Adj x y := x ≠ y ∧ IsSquare (x - y)
  -- (symmetry uses that `-1` is a square mod `p`)

theorem paley_clique (hGRH : PrimitiveDirichletLZerosOnLine) (X : ℝ) :
    ∃ p : ℕ, ∃ _ : Fact p.Prime, ∃ hp : p % 4 = 1, X < p ∧ p % 8 = 1 ∧
      ∃ k : ℕ, Real.log p * Real.log (Real.log p) / 8 < k ∧
        ∃ S : Finset (ZMod p), (paleyGraph p hp).IsNClique k S
```

## Montgomery's theorem (`Paley/Final.lean`, `Paley/Main.lean`)

```lean
theorem many_squares (hGRH : PrimitiveDirichletLZerosOnLine) (X : ℝ) :
    ∃ p : ℕ, p.Prime ∧ X < p ∧ p % 8 = 1 ∧
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.log p * Real.log (Real.log p) / 8 → IsSquare (n : ZMod p)

-- The quantitative core, before choosing `y` in terms of `u`.
-- `modulus y = 8 * ∏ (odd primes q ≤ y)`, `oddPrimes y` = the odd primes `≤ y`, `ψ` = Chebyshev's function.
theorem exists_prime (hGRH : PrimitiveDirichletLZerosOnLine) : ∃ C : ℝ, 0 < C ∧
    ∀ (y : ℕ) (u : ℝ), 4 ≤ u → (y : ℝ) < Real.sqrt u →
      (2 : ℝ) ^ ((oddPrimes y).card + 3) *
          (C * Real.sqrt u * Real.log (modulus y * u) ^ 2 + Real.log (modulus y)
            + 4 * Real.sqrt u * Real.log u + Real.log 4 * Real.sqrt u)
        < ψ u - Real.log (modulus y) - 2 * Real.sqrt u * Real.log u →
      ∃ p : ℕ, p.Prime ∧ Real.sqrt u < p ∧ (p : ℝ) ≤ u ∧ p % 8 = 1 ∧
        ∀ n : ℕ, 0 < n → n ≤ y → IsSquare (n : ZMod p)
```

## Character sums under GRH (`Paley/PsiBound.lean`, `Paley/Main.lean`)

```lean
-- `psi0 χ u = ∑_{1 ≤ n ≤ u} Λ(n) χ(n) - [χ = 1] u` (Alpöge's archive, `GlobalTheoryTheory.psi0`)
theorem psi0_le (hGRH : PrimitiveDirichletLZerosOnLine) : ∃ C : ℝ, 0 < C ∧
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → ∀ u : ℝ, 4 ≤ u →
      ‖GlobalTheoryTheory.psi0 χ u‖ ≤ C * Real.sqrt u * Real.log (N * u) ^ 2

-- Any nontrivial (possibly imprimitive) χ mod M; `R M u` = ∑ of Λ(n) over n ≤ u not coprime to M.
theorem psiChar_le (hGRH : PrimitiveDirichletLZerosOnLine) : ∃ C : ℝ, 0 < C ∧
    ∀ (M : ℕ) [NeZero M] (χ : DirichletCharacter ℂ M), χ ≠ 1 → ∀ u : ℝ, 4 ≤ u →
      ‖∑ k ∈ Ioc 0 ⌊u⌋₊, ((Λ k : ℝ) : ℂ) * χ k‖ ≤ C * Real.sqrt u * Real.log (M * u) ^ 2 + R M u
```

## Unconditional algebra (`Paley/Squares.lean`, `Paley/Count.lean`)

```lean
theorem card_ker_sq_le (y : ℕ) :
    Nat.card (powMonoidHom 2 : (ZMod (modulus y))ˣ →* (ZMod (modulus y))ˣ).ker
      ≤ 2 ^ ((oddPrimes y).card + 3)

theorem isSquare_of_sq_mod {y p : ℕ} (hp : p.Prime) (hpy : y < p)
    (hsq : ∃ b : (ZMod (modulus y))ˣ, ((b ^ 2 : (ZMod (modulus y))ˣ) : ZMod (modulus y)) = p) :
    p % 8 = 1 ∧ ∀ n : ℕ, 0 < n → n ≤ y → IsSquare (n : ZMod p)

-- `sqSub M` = squares in `(ZMod M)ˣ`, `indH M` its indicator on `ZMod M`.
theorem count_ge (s : Finset ℕ) (w : ℕ → ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ χ : DirichletCharacter ℂ M, χ ≠ 1 → ‖∑ k ∈ s, (w k : ℂ) * χ k‖ ≤ B) :
    (Nat.card (sqSub M) : ℝ) * ∑ k ∈ s, w k * ((1 : DirichletCharacter ℂ M) k).re
      - M.totient * B ≤ M.totient * ∑ k ∈ s, w k * indH M k
```
