/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Flat.TorsionFree
public import ReasLib.LinearAlgebra.TensorProduct.RightModule
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Localization
public import ReasLib.RingTheory.Localization.TensorProduct.FractionRing
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated primes after base change to a fraction ring

@stack 05C1

The fraction ring is not fixed to Mathlib's chosen `FractionRing R`: callers may use any
commutative ring carrying an `IsFractionRing R K` structure.  The right-factor tensor action is
scoped, so this leaf does not install a competing global module or algebra instance.
-/

@[expose] public section

open scoped TensorProduct TensorProduct.Right nonZeroDivisors

universe u v w x

namespace associatedPrimesOfModule.BaseChange.FractionRing

variable {R : Type u} {S : Type v} {N : Type w} {K : Type x}
variable [CommRing R] [CommRing K] [Algebra R K] [IsFractionRing R K]
variable [CommRing S] [Algebra R S]
variable [AddCommGroup N] [Module S N] [Module R N] [IsScalarTower R S N]

/-- A flat module has the same exact associated primes after localization at the image of the
non-zero-divisors of the base ring. -/
@[stacks 05C1 "associated primes in the canonical fraction-ring base change"]
theorem eq_localizedModule [Module.Flat R N] :
    associatedPrimesOfModule S N =
      associatedPrimesOfModule S
        (LocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) N) := by
  refine associatedPrimesOfModule.Localization.eq_of_isSMulRegular
    (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) ?_
  intro s
  change Function.Injective (((s : S) • ·) : N → N)
  rcases s.2 with ⟨r, hr, hs⟩
  rw [← hs]
  exact (Module.Flat.isSMulRegular_of_nonZeroDivisors hr).map
    (algebraMap R S) fun m ↦ by simp

/-- The canonical localization and textbook tensor models have the same exact associated primes
over the original algebra. -/
@[stacks 05C1 "associated primes in the two fraction-ring base-change models"]
theorem localizedModule_eq_textbook :
    associatedPrimesOfModule S
        (LocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) N) =
      associatedPrimesOfModule S (N ⊗[R] K) :=
  LinearEquiv.associatedPrimesOfModule_eq S _
    (LocalizedModule.fractionRingBaseChangeEquiv
      (R := R) (S := S) (N := N) (K := K))

/-- Extending a flat module to any chosen fraction ring does not change its exact
associated primes over the original algebra. -/
@[stacks 05C1 "associated primes are unchanged by fraction-ring base change"]
theorem eq [Module.Flat R N] :
    associatedPrimesOfModule S N = associatedPrimesOfModule S (N ⊗[R] K) :=
  (eq_localizedModule (R := R) (S := S) (N := N)).trans
    (localizedModule_eq_textbook (R := R) (S := S) (N := N) (K := K))

omit [Module R N] [IsScalarTower R S N] in
/-- Exact associated primes of the canonical localization model are contractions of those over
the localized algebra. -/
@[stacks 05C1 "associated primes in the canonical localization by contraction"]
theorem localizedModule_eq_image_comap :
    associatedPrimesOfModule S
        (LocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) N) =
      Ideal.comap
          (algebraMap S
            (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)))) ''
        associatedPrimesOfModule
          (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)))
          (LocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) N) := by
  simpa using
    (associatedPrimesOfModule_localizedModule_eq_image_comap
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) (M := N)).symm

/-- Associated primes after fraction-ring base change, viewed over the original algebra, are the
contractions of associated primes over the base-changed algebra. -/
@[stacks 05C1 "associated primes after fraction-ring base change by contraction"]
theorem baseChange_eq_image_comap :
    associatedPrimesOfModule S (N ⊗[R] K) =
      Ideal.comap
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] K) ''
        associatedPrimesOfModule (S ⊗[R] K) (N ⊗[R] K) := by
  change associatedPrimesOfModule S (N ⊗[R] K) =
    Ideal.comap (algebraMap S (S ⊗[R] K)) ''
      associatedPrimesOfModule (S ⊗[R] K) (N ⊗[R] K)
  exact
    (associatedPrimesOfModule_image_comap_eq_of_isLocalization
      (R := S) (A := S ⊗[R] K) (M := N ⊗[R] K)
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))).symm

/-- Combined fraction-ring base-change formula for exact associated primes. -/
@[stacks 05C1 "associated primes as contractions after fraction-ring base change"]
theorem eq_image_comap [Module.Flat R N] :
    associatedPrimesOfModule S N =
      Ideal.comap
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] K) ''
        associatedPrimesOfModule (S ⊗[R] K) (N ⊗[R] K) := by
  exact (eq (R := R) (S := S) (N := N) (K := K)).trans
    (baseChange_eq_image_comap (R := R) (S := S) (N := N) (K := K))

/-- Noetherian specialization of `eq_localizedModule` in Mathlib's associated-prime API. -/
@[stacks 05C1 "Noetherian associated primes in the canonical fraction-ring base change"]
theorem associatedPrimes_eq_localizedModule [Module.Flat R N] [IsNoetherianRing S] :
    associatedPrimes S N =
      associatedPrimes S
        (LocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) N) := by
  simpa only [← associatedPrimesOfModule_eq_associatedPrimes] using
    (eq_localizedModule (R := R) (S := S) (N := N))

/-- Noetherian specialization of `eq` in Mathlib's associated-prime API. -/
@[stacks 05C1 "Noetherian associated primes under fraction-ring base change"]
theorem associatedPrimes_eq [Module.Flat R N] [IsNoetherianRing S] :
    associatedPrimes S N = associatedPrimes S (N ⊗[R] K) := by
  simpa only [← associatedPrimesOfModule_eq_associatedPrimes] using
    (eq (R := R) (S := S) (N := N) (K := K))

/-- Noetherian specialization of `localizedModule_eq_textbook` in Mathlib's associated-prime
API. -/
@[stacks 05C1 "Noetherian associated primes in the two fraction-ring base-change models"]
theorem associatedPrimes_localizedModule_eq_textbook [IsNoetherianRing S] :
    associatedPrimes S
        (LocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) N) =
      associatedPrimes S (N ⊗[R] K) := by
  simpa only [← associatedPrimesOfModule_eq_associatedPrimes] using
    (localizedModule_eq_textbook (R := R) (S := S) (N := N) (K := K))

omit [Module R N] [IsScalarTower R S N] in
/-- Noetherian specialization of `localizedModule_eq_image_comap` in Mathlib's associated-prime
API. -/
@[stacks 05C1 "Noetherian associated primes in the canonical localization by contraction"]
theorem associatedPrimes_localizedModule_eq_image_comap [IsNoetherianRing S] :
    associatedPrimes S
        (LocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) N) =
      Ideal.comap
          (algebraMap S
            (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)))) ''
        associatedPrimes
          (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)))
          (LocalizedModule (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) N) := by
  letI : IsNoetherianRing
      (Localization (Algebra.algebraMapSubmonoid S (nonZeroDivisors R))) :=
    IsLocalization.isNoetherianRing
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) _ inferInstance
  simpa only [← associatedPrimesOfModule_eq_associatedPrimes] using
    (localizedModule_eq_image_comap (R := R) (S := S) (N := N))

/-- Noetherian specialization of `baseChange_eq_image_comap` in Mathlib's associated-prime API. -/
@[stacks 05C1 "Noetherian associated primes after fraction-ring base change by contraction"]
theorem associatedPrimes_baseChange_eq_image_comap [IsNoetherianRing S] :
    associatedPrimes S (N ⊗[R] K) =
      Ideal.comap
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] K) ''
        associatedPrimes (S ⊗[R] K) (N ⊗[R] K) := by
  letI : IsNoetherianRing (S ⊗[R] K) :=
    IsLocalization.isNoetherianRing
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) _ inferInstance
  simpa only [← associatedPrimesOfModule_eq_associatedPrimes] using
    (baseChange_eq_image_comap (R := R) (S := S) (N := N) (K := K))

/-- Noetherian specialization of `eq_image_comap` in Mathlib's associated-prime API. -/
@[stacks 05C1 "Noetherian associated primes as contractions after fraction-ring base change"]
theorem associatedPrimes_eq_image_comap [Module.Flat R N] [IsNoetherianRing S] :
    associatedPrimes S N =
      Ideal.comap
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] K) ''
        associatedPrimes (S ⊗[R] K) (N ⊗[R] K) := by
  letI : IsNoetherianRing (S ⊗[R] K) :=
    IsLocalization.isNoetherianRing
      (Algebra.algebraMapSubmonoid S (nonZeroDivisors R)) _ inferInstance
  simpa only [← associatedPrimesOfModule_eq_associatedPrimes] using
    (eq_image_comap (R := R) (S := S) (N := N) (K := K))

end associatedPrimesOfModule.BaseChange.FractionRing
