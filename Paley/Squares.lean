import Mathlib

/-!
# The modulus `M = 8 ∏_{3 ≤ q ≤ y} q` and squares

* `card_ker_sq_le` : the squaring map on `(ZMod M)ˣ` has kernel of size `≤ 2 ^ (#odd primes ≤ y + 3)`.
* `isSquare_of_sq_mod` : if a prime `p > y` is a square unit mod `M`, then `p % 8 = 1` and every
  `1 ≤ n ≤ y` is a square mod `p` (quadratic reciprocity).
-/

open Finset

namespace Paley

/-- Odd primes `≤ y`. -/
def oddPrimes (y : ℕ) : Finset ℕ := (range (y + 1)).filter (fun q => q.Prime ∧ q ≠ 2)

/-- The modulus `8 ∏_{q odd prime ≤ y} q`. -/
def modulus (y : ℕ) : ℕ := 8 * ∏ q ∈ oddPrimes y, q

theorem mem_oddPrimes {y q : ℕ} : q ∈ oddPrimes y ↔ q ≤ y ∧ q.Prime ∧ q ≠ 2 := by
  simp [oddPrimes]

theorem prod_oddPrimes_pos (y : ℕ) : 0 < ∏ q ∈ oddPrimes y, q :=
  prod_pos fun q hq => (mem_oddPrimes.1 hq).2.1.pos

theorem modulus_pos (y : ℕ) : 0 < modulus y := by
  unfold modulus; have := prod_oddPrimes_pos y; positivity

instance (y : ℕ) : NeZero (modulus y) := ⟨(modulus_pos y).ne'⟩

theorem dvd_modulus_of_mem {y q : ℕ} (hq : q ∈ oddPrimes y) : q ∣ modulus y :=
  dvd_mul_of_dvd_right (dvd_prod_of_mem _ hq) 8

theorem eight_dvd_modulus (y : ℕ) : 8 ∣ modulus y := dvd_mul_right 8 _

theorem coprime_eight_prod (y : ℕ) : Nat.Coprime 8 (∏ q ∈ oddPrimes y, q) := by
  refine Nat.Coprime.prod_right fun q hq => ?_
  obtain ⟨-, hp, h2⟩ := mem_oddPrimes.1 hq
  have : Nat.Coprime 2 q := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm h2)
  simpa using Nat.Coprime.pow_left 3 this

/-- Divisibility by the modulus from divisibility by its prime-power factors. -/
theorem modulus_dvd_of {y v : ℕ} (h8 : 8 ∣ v) (hq : ∀ q ∈ oddPrimes y, q ∣ v) : modulus y ∣ v := by
  refine Nat.Coprime.mul_dvd_of_dvd_of_dvd (coprime_eight_prod y) h8 ?_
  refine Finset.prod_primes_dvd v (fun q hq' => ?_) hq
  exact (mem_oddPrimes.1 hq').2.1.prime

/-- CRT injectivity: an element of `ZMod M` is determined by its reductions mod `8` and mod each `q`. -/
theorem eq_of_casts {y : ℕ} {a b : ZMod (modulus y)}
    (h8 : (ZMod.cast a : ZMod 8) = ZMod.cast b)
    (hq : ∀ q : oddPrimes y, (ZMod.cast a : ZMod (q : ℕ)) = ZMod.cast b) : a = b := by
  have key : ∀ d, d ∣ modulus y → (ZMod.cast (a - b) : ZMod d) = 0 → d ∣ (a - b).val := by
    intro d hd h
    rw [← ZMod.natCast_zmod_val (a - b), ZMod.cast_natCast hd] at h
    exact (ZMod.natCast_eq_zero_iff _ _).1 h
  have hcast : ∀ d, d ∣ modulus y → (ZMod.cast (a - b) : ZMod d) = ZMod.cast a - ZMod.cast b := by
    intro d hd
    exact map_sub (ZMod.castHom hd (ZMod d)) a b
  have hv : modulus y ∣ (a - b).val := by
    refine modulus_dvd_of (key 8 (eight_dvd_modulus y) ?_) (fun q hq' => ?_)
    · rw [hcast 8 (eight_dvd_modulus y), h8, sub_self]
    · refine key q (dvd_modulus_of_mem hq') ?_
      rw [hcast q (dvd_modulus_of_mem hq'), hq ⟨q, hq'⟩, sub_self]
  have : a - b = 0 := by
    rw [← ZMod.natCast_zmod_val (a - b), ZMod.natCast_eq_zero_iff]; exact hv
  exact sub_eq_zero.1 this

/-- The kernel of squaring on `(ZMod M)ˣ` is small. -/
theorem card_ker_sq_le (y : ℕ) :
    Nat.card (powMonoidHom 2 : (ZMod (modulus y))ˣ →* (ZMod (modulus y))ˣ).ker
      ≤ 2 ^ ((oddPrimes y).card + 3) := by
  classical
  set M := modulus y
  let f : (ZMod M)ˣ → ZMod 8 × ((q : oddPrimes y) → ZMod (q : ℕ)) :=
    fun a => (ZMod.cast (a : ZMod M), fun q => ZMod.cast (a : ZMod M))
  have hinj : Function.Injective f := by
    intro a b h
    simp only [f, Prod.mk.injEq, funext_iff] at h
    exact Units.ext (eq_of_casts h.1 h.2)
  set S : Finset (ZMod 8 × ((q : oddPrimes y) → ZMod (q : ℕ))) :=
    (univ : Finset (ZMod 8)) ×ˢ Fintype.piFinset (fun _ => ({1, -1} : Finset _))
  have hmaps : ∀ a ∈ (powMonoidHom 2 : (ZMod M)ˣ →* (ZMod M)ˣ).ker, f a ∈ S := by
    intro a ha
    rw [MonoidHom.mem_ker, powMonoidHom_apply] at ha
    simp only [S, f, mem_product, mem_univ, true_and, Fintype.mem_piFinset]
    intro q
    obtain ⟨-, hp, -⟩ := mem_oddPrimes.1 q.2
    have : Fact (q : ℕ).Prime := ⟨hp⟩
    have h1 : ((a : ZMod M) * a) = 1 := by
      rw [← Units.val_mul, ← sq, ha, Units.val_one]
    have h2 : (ZMod.cast (a : ZMod M) : ZMod (q : ℕ)) * ZMod.cast (a : ZMod M) = 1 := by
      have := congrArg (ZMod.castHom (dvd_modulus_of_mem q.2) (ZMod (q : ℕ))) h1
      rw [map_mul, map_one] at this
      exact this
    rcases mul_self_eq_one_iff.1 h2 with h | h <;> simp [h]
  calc Nat.card (powMonoidHom 2 : (ZMod M)ˣ →* (ZMod M)ˣ).ker
      = Fintype.card (powMonoidHom 2 : (ZMod M)ˣ →* (ZMod M)ˣ).ker := Nat.card_eq_fintype_card
    _ ≤ S.card := by
      rw [← Finset.card_univ]
      refine Finset.card_le_card_of_injOn (fun a => f a) (fun a _ => hmaps a a.2) ?_
      intro a _ b _ h
      exact Subtype.ext (hinj h)
    _ ≤ 8 * 2 ^ (oddPrimes y).card := by
      simp only [S, card_product, card_univ, ZMod.card, Fintype.card_piFinset]
      gcongr
      calc ∏ q : oddPrimes y, ({1, -1} : Finset (ZMod (q : ℕ))).card ≤ ∏ _q : oddPrimes y, 2 :=
            Finset.prod_le_prod' fun _ _ => Finset.card_le_two
        _ = 2 ^ (oddPrimes y).card := by simp
    _ = 2 ^ ((oddPrimes y).card + 3) := by ring

/-- The squaring map: `|G| = |ker| · |range|`. -/
theorem card_units_eq (y : ℕ) :
    (modulus y).totient = Nat.card (powMonoidHom 2 : (ZMod (modulus y))ˣ →* (ZMod (modulus y))ˣ).ker
      * Nat.card (powMonoidHom 2 : (ZMod (modulus y))ˣ →* (ZMod (modulus y))ˣ).range := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient]

theorem units_eight_sq (c : (ZMod 8)ˣ) : c ^ 2 = 1 := by
  revert c; decide

/-- If a prime `p > y` is a square unit modulo `M`, then `p ≡ 1 (mod 8)` and every
`1 ≤ n ≤ y` is a square mod `p`. -/
theorem isSquare_of_sq_mod {y p : ℕ} (hp : p.Prime) (hpy : y < p)
    (hsq : ∃ b : (ZMod (modulus y))ˣ, ((b ^ 2 : (ZMod (modulus y))ˣ) : ZMod (modulus y)) = p) :
    p % 8 = 1 ∧ ∀ n : ℕ, 0 < n → n ≤ y → IsSquare (n : ZMod p) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hb⟩ := hsq
  -- mod 8
  have h8 : (p : ZMod 8) = 1 := by
    have := congrArg (ZMod.castHom (eight_dvd_modulus y) (ZMod 8)) hb
    rw [map_natCast] at this
    rw [← this, Units.val_pow_eq_pow_val, map_pow]
    have hu := congrArg Units.val
      (units_eight_sq (Units.map (ZMod.castHom (eight_dvd_modulus y) (ZMod 8)).toMonoidHom b))
    rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.val_one] at hu
    exact hu
  have hp8 : p % 8 = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' p 1 8).1 (by simpa using h8)
    simpa using this
  refine ⟨hp8, ?_⟩
  have hp4 : p % 4 = 1 := by omega
  have hp2 : p ≠ 2 := by omega
  -- each prime `r ≤ y` is a square mod `p`
  have hprime : ∀ r : ℕ, r.Prime → r ≤ y → IsSquare (r : ZMod p) := by
    intro r hr hry
    by_cases hr2 : r = 2
    · subst hr2
      simpa using (ZMod.exists_sq_eq_two_iff hp2).2 (Or.inl hp8)
    have : Fact r.Prime := ⟨hr⟩
    have hrM : r ∈ oddPrimes y := mem_oddPrimes.2 ⟨hry, hr, hr2⟩
    -- `p` is a square mod `r`
    have hpr : IsSquare (p : ZMod r) := by
      have := congrArg (ZMod.castHom (dvd_modulus_of_mem hrM) (ZMod r)) hb
      rw [map_natCast] at this
      rw [← this]
      refine ⟨ZMod.castHom (dvd_modulus_of_mem hrM) (ZMod r) (b : ZMod (modulus y)), ?_⟩
      rw [Units.val_pow_eq_pow_val, map_pow, sq]
    have hpr0 : (p : ZMod r) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := (Nat.prime_dvd_prime_iff_eq hr hp).1 h
      omega
    have hrp0 : (r : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      have := Nat.le_of_dvd hr.pos h
      omega
    have h1 : legendreSym r p = 1 := (legendreSym.eq_one_iff' r hpr0).2 hpr
    have h2 : legendreSym p r = 1 := by
      rw [← legendreSym.quadratic_reciprocity_one_mod_four hp4 hr2]; exact h1
    exact (legendreSym.eq_one_iff' p hrp0).1 h2
  intro n hn hny
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with h | h
    · obtain rfl : n = 1 := by omega
      simp
    · set r := n.minFac
      have hr : r.Prime := Nat.minFac_prime (by omega)
      have hrn : r ∣ n := Nat.minFac_dvd n
      obtain ⟨m, hm⟩ := hrn
      have hm0 : 0 < m := by rcases Nat.eq_zero_or_pos m with h0 | h0 <;> [simp [h0] at hm; exact h0] <;> omega
      have hmn : m < n := by
        rw [hm]; have := hr.two_le; nlinarith
      have hrle : r ≤ n := Nat.minFac_le (by omega)
      rw [hm, Nat.cast_mul]
      exact (hprime r hr (hrle.trans hny)).mul (ih m hmn hm0 (by omega))

end Paley
