# Notes: method, measurements, and caveats

## The argument (Montgomery 1971)

Fix $y$ and let $M = 8\prod_{3 \le q \le y} q$ (`Paley/Squares.lean`, `modulus`). Let $H \le (\mathbb Z/M)^\times$ be the subgroup of squares.

- **Squares mod $M$ give many small squares mod $p$** (`isSquare_of_sq_mod`). If a prime $p > y$ is a square unit mod $M$, then $p$ is a square mod $8$, so $p \equiv 1 \pmod 8$. That makes $-1$ and $2$ squares mod $p$. For each odd prime $q \le y$, $p$ is a square mod $q$, and quadratic reciprocity (with $p \equiv 1 \bmod 4$) turns $(p/q) = 1$ into $(q/p) = 1$. Every $1 \le n \le y$ is a product of such primes, so it is a square mod $p$.
- **$H$ has small index** (`card_ker_sq_le`, `card_units_eq`). The index of $H$ equals the number of solutions of $a^2 = 1$ in $(\mathbb Z/M)^\times$. By CRT injectivity into $\mathbb Z/8 \times \prod_q \mathbb Z/q$ and $a \equiv \pm 1 \pmod q$, this is at most $8 \cdot 2^{k}$, where $k$ is the number of odd primes $q \le y$.
- **Counting primes in $H$** (`Paley/Count.lean`). With $c_\chi = \sum_{a \in H}\chi(a^{-1})$, orthogonality gives $\varphi(M)\,\mathbf 1_H(n) = \sum_\chi c_\chi \chi(n)$. Each $c_\chi$ is $0$ or $|H|$, and $\sum_\chi c_\chi = \varphi(M)$. So the weighted count over $H$ is at least $\frac{|H|}{\varphi(M)}\psi_{\chi_0}(u) - \max_{\chi \ne 1}\lvert\psi_\chi(u)\rvert$. The number of characters ($2^{\pi(y)}$-ish) never enters the error, only the index.
- **GRH** (`Paley/PsiBound.lean`, `psiChar_le`). For primitive $\chi$ mod $N$, Alpöge's archive provides the truncated explicit formula and the zero count $N(t+1) - N(t) \ll \log(N(|t|+2))$, both with absolute constants. On the critical line $\lvert u^\rho\rvert = \sqrt u$, and with $T = \sqrt u$ this gives $\lvert\psi_0(u,\chi)\rvert \le C\sqrt u\log^2(Nu)$. An imprimitive $\chi$ differs from its primitive character only at $n$ not coprime to $M$. Those contribute at most $\log M + 2\sqrt u\log u$ (primes dividing $M$, plus Mathlib's $\psi - \theta \le 2\sqrt x\log x$).
- **Extracting a prime** (`SH_le`, `exists_prime`). Prime powers and primes $\le \sqrt u$ contribute at most $(\log 4 + 2\log u)\sqrt u$. So if $[\,(\mathbb Z/M)^\times : H\,] \cdot \sqrt u \cdot \mathrm{polylog}$ is smaller than $\psi(u) \approx u$, some prime $p \in (\sqrt u, u]$ lies in $H$.
- **Choosing $y$** (`Paley/Final.lean`). Take $y = \lfloor \log u \cdot \log\log u / 8\rfloor$. Mathlib's $\pi(x) \le (\log 4 + 1)\,x/\log x$ (eventually) gives $k \log 2 \le \log u / 4$, so the index is at most $8u^{1/4}$. The closing inequality `closing` is then elementary: $\log^4 u = o(u^{1/4})$, $\log^2 u \le \sqrt u$, $\log M \le \log^2 u$, and Chebyshev's $\psi(u) \ge (u-1)\log 2 - \log(u+2)$. Since $p \le u$, every $n \le \tfrac18\log p \cdot \log\log p$ satisfies $n \le y$.

The constant: $1/8$ is chosen for convenience. With $\pi(x) \sim x/\log x$ the same argument allows any $c < 1/(4\log 2)$.

## What is and is not new

The statement that $n_2(p) > c \log p \cdot \log\log p$ for infinitely many primes $p$ was previously proved only assuming GRH (Montgomery). Unconditionally the best published bound was $\gg \log p \cdot \log\log\log p$ (Graham–Ringrose). Alpöge's theorem makes Montgomery's result unconditional, and this repository is a formal proof of that. The argument itself is Montgomery's. Alpöge's methods (theta-lift chains, slope inequalities) are not used, only his final theorem and the analytic lemmas in his archive.

## Trust model

- Everything in this repository is checked by Lean's kernel, with `#print axioms` reporting only `[propext, Classical.choice, Quot.sound]` for every theorem. `leanchecker` independently replays this repository's modules.
- The build imports Alpöge's archive (`riemann-hypothesis` @ `f28a764`), restored from the community cache (SHA-256 pinned). We do not rebuild or re-check it, and Lean does not re-check imported `.olean` files. The conditional modules import only the parts they need (`Statements` and the explicit-formula files under `Development/AbelianVarietyTheory/Proofs/`). `Unconditional.lean` imports `Main`, so it loads the whole archive.

## Reproduction details

- `reproduce.sh all` builds against `riemann-hypothesis` @ `f28a764` (Lean `v4.33.1`):
  - Restoring the cache requires a clean checkout, so this repository's files are added afterward.
  - Building the six `Paley` modules takes a few minutes. `Unconditional.lean` takes about 10 minutes natively and peaks at around 12 GB of RAM.
  - `leanchecker` runs one module per process.
- **Docker Desktop (macOS) caveats** (same as [grh-miller](https://github.com/amrehan/grh-miller)):
  1. Docker Desktop's Linux VM defaults to 8 MB readahead on its virtual disks. The unconditional import memory-maps ~90 GB, so `docker-reproduce.sh` lowers readahead to 128 KB using a throwaway privileged container. This only happens on Docker Desktop, never on a native Linux host's disks.
  2. Docker Desktop's network stack occasionally drops connections during the parallel cache downloads. `reproduce.sh` hashes every archive against the pinned SHA-256 manifest (`scripts/verify-rh-cache.py`), deletes corrupted files, and retries.
  3. `PALEY_VOLUME` and `PALEY_CACHE_VOLUME` choose the Docker volumes for the work directory and the download cache. Pointing `PALEY_VOLUME` at a volume that already holds a restored `riemann-hypothesis` checkout skips the ~110 GB download.
