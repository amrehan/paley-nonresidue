# Large Least Quadratic Non-Residues and Paley Cliques from GRH (Lean 4)

This repository contains a Lean 4 / Mathlib formalization of **Montgomery's theorem (1971)**: assuming the Generalized Riemann Hypothesis (GRH) for Dirichlet $L$-functions, there are infinitely many primes $p$ whose least quadratic non-residue exceeds $c \log p \log\log p$. By connecting to Levent Alpöge's Lean proof of GRH ([leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis)), the result is also established **unconditionally**, together with the corresponding bound for cliques in Paley graphs. It was developed with assistance from Claude Opus (Anthropic). Correctness does not rest on that, since every theorem is checked by Lean's kernel.

### What's formalized

- **Many small squares:** For every $X$ there is a prime $p > X$ with $p \equiv 1 \pmod 8$ such that every $1 \le n \le \tfrac18 \log p \log\log p$ is a square modulo $p$.
- **Least quadratic non-residue:** For infinitely many primes $p$, every quadratic non-residue $n$ mod $p$ satisfies $n > \tfrac18 \log p \log\log p$.
- **Paley graphs:** For every $X$ there is a prime $p > X$, $p \equiv 1 \pmod 8$, whose Paley graph contains a clique with more than $\tfrac18 \log p \log\log p$ vertices (namely $\{0, 1, \dots, k\}$).
- **GRH square-root bound, uniform in the modulus:** $\bigl|\sum_{n \le u} \Lambda(n)\chi(n) - [\chi = 1]\,u\bigr| \le C \sqrt u \,\log^2(Nu)$ for every primitive $\chi$ mod $N$ and $u \ge 4$.

Unconditionally, the previous best bound for both the least non-residue and the Paley clique number (infinitely often) was of order $\log p \log\log\log p$ (Graham–Ringrose 1990). Montgomery's $\log p \log\log p$ was known only under GRH.

Every theorem depends only on the standard Lean axioms (`[propext, Classical.choice, Quot.sound]`): no `sorry`, no `native_decide`, and no extra axioms. You can browse the exact Lean statements in **[STATEMENTS.md](STATEMENTS.md)**.

## Scope and limitations

- **No new math:** This is a formalization of Montgomery's 1971 argument, made unconditional by Alpöge's theorem. The unconditional statement is new only because GRH is now a theorem. The insight in Alpöge's proof (theta-lift chains standing in for Stepanov's auxiliary polynomials) is not used here. Only its conclusion is.
- **The constant:** We prove the bound with $c = 1/8$. The argument gives any $c < 1/(4\log 2) \approx 0.36$ with a sharper prime-counting bound. We use Mathlib's Chebyshev bound $\pi(x) \le (\log 4 + 1)\,x/\log x$ for large $x$.
- **Ineffective in $X$:** The analytic constant $C$ comes from existential statements in Alpöge's archive, so the theorems say "for every $X$ there is $p > X$" without an explicit bound on $p$.
- **Hypothesis:** The conditional results assume *only* `PrimitiveDirichletLZerosOnLine` (GRH for primitive Dirichlet $L$-functions), taken verbatim from Alpöge's `src/Statements.lean`.

## Usage

```lean
import Paley
open Paley

-- Conditional form: every theorem takes `hGRH : PrimitiveDirichletLZerosOnLine`
example (hGRH : PrimitiveDirichletLZerosOnLine) (X : ℝ) :
    ∃ p : ℕ, p.Prime ∧ X < p ∧ p % 8 = 1 ∧
      ∀ n : ℕ, 0 < n → (n : ℝ) ≤ Real.log p * Real.log (Real.log p) / 8 → IsSquare (n : ZMod p) :=
  many_squares hGRH X
```

The unconditional versions live in [`Unconditional/Unconditional.lean`](Unconditional/Unconditional.lean). That file is built inside Alpöge's archive and applies each conditional theorem to his `LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine`.

## Trust model

- **Conditional and unconditional results both** depend on Mathlib, Alpöge's archive and this repository. Unlike [grh-miller](https://github.com/amrehan/grh-miller), even the conditional theorems need the archive: the truncated explicit formula and the zero-counting bound, both uniform in the modulus, are taken from its `Development` library. Everything in this repository is checked by Lean's kernel and independently replayed with `leanchecker`.
- **The archive** is restored from the community `.olean` cache at a pinned commit, following that project's recommendation, rather than rebuilt from scratch. Because Lean does not re-check imported `.olean` files, `leanchecker` only replays the modules in this repository.

## Reproducing the build

```sh
./reproduce.sh all             # Alpöge's archive via the community cache: ~110 GB disk, ~12 GB RAM, ~1 h
./docker-reproduce.sh all      # Same in Docker (Ubuntu 24.04): ~210 GB disk, ~18 GB RAM
```

The upstream commit is pinned in `reproduce.sh`. The script will fail on any Lean error, any missing `#print axioms` output, or any axiom outside the standard three. Docker-specific notes (the disk readahead fix for Docker Desktop and retrying dropped downloads) are covered in [NOTES.md](NOTES.md).

## Repository layout

| Path | Description |
| --- | --- |
| `Paley/PsiBound.lean` | GRH ⇒ $\lvert\psi_0(u,\chi)\rvert \le C\sqrt u\log^2(Nu)$ for primitive $\chi$, uniform in $N$ |
| `Paley/Squares.lean` | The modulus $M = 8\prod_{3 \le q \le y} q$; the kernel of squaring on $(\mathbb Z/M)^\times$ has size $\le 2^{\#\{q\} + 3}$; quadratic reciprocity: a prime that is a square unit mod $M$ has all of $1, \dots, y$ as squares |
| `Paley/Count.lean` | Counting in the subgroup of squares by character orthogonality |
| `Paley/Main.lean` | Imprimitive vs. primitive characters; Montgomery's argument: a prime $p \in (\sqrt u, u]$ that is a square unit mod $M$ |
| `Paley/Final.lean` | The choice $y = \lfloor \log u \log\log u / 8\rfloor$ and the asymptotics; `many_squares` |
| `Paley/Clique.lean` | Paley graphs and `paley_clique` |
| `Unconditional/Unconditional.lean` | Unconditional theorems via Alpöge's `LFunction_eq_zero_re_of_isPrimitive` |
| `scripts/AxiomsConditional.lean` | `#print axioms` for the conditional theorems |

## Credits

- **Mathematics:** H. L. Montgomery, *Topics in Multiplicative Number Theory*, LNM 227 (1971), where the bound $n_2(p) \gg \log p \log\log p$ infinitely often is proved under GRH; S. W. Graham and C. J. Ringrose, *Lower bounds for least quadratic non-residues* (1990), the previous unconditional bound.
- **GRH for Dirichlet $L$-functions in Lean:** Levent Alpöge, via [leanprover-community/riemann-hypothesis](https://github.com/leanprover-community/riemann-hypothesis). The hypothesis is his `PrimitiveDirichletLZerosOnLine`, and the explicit formula and zero counting come from his archive's `Development` library.
- **Related:** [amrehan/grh-miller](https://github.com/amrehan/grh-miller) (deterministic Miller test and Bach's constant from the same GRH formalization).

## License

Apache-2.0 (see [LICENSE](LICENSE)). Copyright 2026.
