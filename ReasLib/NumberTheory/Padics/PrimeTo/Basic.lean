module

public import Mathlib.Algebra.Group.Pi.Units
public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.NumberTheory.Divisors
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Prime-to-`q` adic integers

The product `∏_{ℓ ∤ q} ℤ_[ℓ]`, together with reduction maps to `ZMod m` for
`m` coprime to `q` and the canonical unit `q`.
-/

@[expose] public section

noncomputable section

namespace PadicInt

/-- Primes that do not divide `q`, used as the index set of `PadicInt.PrimeTo q`. -/
abbrev PrimeTo.Index (q : ℕ) : Type :=
  {p : Nat.Primes // ¬ p.val ∣ q}

/-- Each index of `PadicInt.PrimeTo q` is a prime number. -/
instance instFactPrime_index (q : ℕ) (p : PrimeTo.Index q) : Fact p.1.val.Prime :=
  ⟨p.1.property⟩

/-- The product `∏_{ℓ ∤ q} ℤ_[ℓ]` of `ℓ`-adic integers for primes `ℓ` not dividing `q`. -/
abbrev PrimeTo (q : ℕ) : Type :=
  ∀ p : PrimeTo.Index q, ℤ_[p.1.val]

namespace PrimeTo

/-- The prime factor `p` of `m` as an index of `PadicInt.PrimeTo q`, using that `m` is
coprime to `q`. -/
def indexOfPrimeFactor (q m : ℕ) [NeZero m] (hm : m.Coprime q) (p : m.primeFactors) :
    Index q :=
  ⟨⟨p.val, Nat.prime_of_mem_primeFactors p.property⟩,
    (Nat.prime_of_mem_primeFactors p.property).coprime_iff_not_dvd.mp
      (hm.coprime_dvd_left (Nat.dvd_of_mem_primeFactors p.property))⟩

/-- Componentwise reduction of `PadicInt.PrimeTo q` along the `p`-adic factor. -/
def toZModPowAt (q : ℕ) (p : Index q) (k : ℕ) :
    PrimeTo q →+* ZMod (p.1.val ^ k) :=
  (PadicInt.toZModPow k).comp (Pi.evalRingHom (fun i : Index q ↦ ℤ_[i.1.val]) p)

/-- Reduction `PadicInt.PrimeTo q →+* ZMod m` assembled from componentwise
`PadicInt.toZModPow` maps and the Chinese remainder isomorphism `ZMod.equivPi`. -/
def toZMod (q m : ℕ) [NeZero m] (hm : m.Coprime q) : PrimeTo q →+* ZMod m :=
  (ZMod.equivPi m (NeZero.ne m)).symm.toRingHom.comp <|
    RingHom.pi fun p ↦ toZModPowAt q (indexOfPrimeFactor q m hm p) (m.factorization p.val)

/-- On a prime-power factor of `m`, `toZMod` recovers `PadicInt.toZModPow` of the
corresponding component. -/
theorem toZMod_comp_eval (q m : ℕ) [NeZero m] (hm : m.Coprime q)
    (x : PrimeTo q) (p : m.primeFactors) :
    ZMod.equivPi m (NeZero.ne m) (toZMod q m hm x) p =
      PadicInt.toZModPow (m.factorization p.val) (x (indexOfPrimeFactor q m hm p)) := by
  simp [toZMod, toZModPowAt, RingHom.comp_apply]
  rfl

/-- The natural number `q` as a unit of `PadicInt.PrimeTo q`, using that `q` is a
unit in each `ℤ_[ℓ]` for `ℓ ∤ q`. -/
def natCastUnit (q : ℕ) [NeZero q] : (PrimeTo q)ˣ :=
  (Pi.isUnit_iff.mpr fun p ↦
    PadicInt.isUnit_iff.mpr
      (PadicInt.norm_natCast_eq_one_iff.mpr
        (p.1.property.coprime_iff_not_dvd.mpr p.property))).unit

/-- The underlying ring element of `natCastUnit q` is `q`. -/
theorem natCastUnit_val (q : ℕ) [NeZero q] : (natCastUnit q).val = q := sorry

/-- The trivial-coefficient congruence `q ^ n - (q * u) ^ n ≡ ∑_{d ∣ n} d * Nat.card (S d)`
in `ZMod m`, for `m` coprime to `q`. -/
def trivialModuleCongruence (q n m : ℕ) [NeZero m] (hm : m.Coprime q)
    (u : (PrimeTo q)ˣ) (S : ℕ → Type) [∀ d, Finite (S d)] : Prop :=
  toZMod q m hm ((q : PrimeTo q) ^ n - ((q : PrimeTo q) * u.val) ^ n) =
    ∑ d ∈ n.divisors, (d * Nat.card (S d) : ZMod m)

end PrimeTo

end PadicInt
