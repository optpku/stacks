/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AlgHom.FlatFiniteType.Factorisation
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic

/-!
# Factorizations between discrete valuation rings

The source and target DVRs are parameters because they stay fixed under later
blowup constructions. A value of `Algebra.DVR.Factorization R L` owns only the
changing intermediate algebra and its map to `L`; properties of the composite
map `R → L`, such as weak ramification, belong on results that use them.
-/

@[expose] public section

open Ideal IsLocalRing

universe u v w

namespace Algebra

/-- Situation 16.4.1 (tag 0BJ2): the reusable factorization datum underlying a
diagram `R → A → L`, with `R → A` flat and of finite type. The invariant DVRs
`R` and `L` are parameters; hypotheses on the composite map `R → L` are kept
separate from this datum. -/
@[stacks 0BJ2]
abbrev DVR.Factorization
    (R : Type u) (L : Type v)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
    [Algebra R L] :=
  AlgHom.Factorisation.FlatFiniteType.{u, u, v, w} (Algebra.ofId R L)

namespace DVR.Factorization

variable {R : Type u} {L : Type v}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
variable [Algebra R L]

/-- Build a DVR factorization from a flat finite-type intermediate algebra and
its map to the target DVR. -/
@[stacks 0BJ2 "DVR factorization constructor"]
def of {B : Type w} [CommRing B] [Algebra R B] [Module.Flat R B]
    [Algebra.FiniteType R B] (toTarget : B →ₐ[R] L) :
    Algebra.DVR.Factorization R L :=
  AlgHom.Factorisation.FlatFiniteType.ofId toTarget

/-- The midpoint supplied to `DVR.Factorization.of` is recovered by
projection. -/
@[simp]
theorem mid_of {B : Type w} [CommRing B] [Algebra R B] [Module.Flat R B]
    [Algebra.FiniteType R B] (toTarget : B →ₐ[R] L) :
    (of toTarget).mid = B := sorry

/-- The target map supplied to `DVR.Factorization.of` is recovered by
projection. -/
@[simp]
theorem toTarget_of {B : Type w} [CommRing B] [Algebra R B]
    [Module.Flat R B] [Algebra.FiniteType R B] (toTarget : B →ₐ[R] L) :
    (of toTarget).toTarget = toTarget := sorry

/-- The flatness, finite-type property, and structural-map compatibility
carried by a DVR factorization. -/
@[stacks 0BJ2 "DVR factorization specification"]
theorem spec (S : Algebra.DVR.Factorization R L) :
    Module.Flat R S.mid ∧ Algebra.FiniteType R S.mid ∧
      S.toTarget.toRingHom.comp (algebraMap R S.mid) = algebraMap R L := sorry

/-- The factorization map induces the canonical `A`-algebra structure on `L`. -/
noncomputable instance (S : Algebra.DVR.Factorization R L) : Algebra S.mid L :=
  S.toTarget.toAlgebra

/-- The generic-center ideal, namely the kernel of the target map. -/
@[stacks 0BJ2 "generic center"]
def genericIdeal (S : Algebra.DVR.Factorization R L) : Ideal S.mid :=
  RingHom.ker S.toTarget.toRingHom

/-- The closed-center ideal, namely the inverse image of the target maximal
ideal. -/
@[stacks 0BJ2 "closed center"]
def closedIdeal (S : Algebra.DVR.Factorization R L) : Ideal S.mid :=
  Ideal.comap S.toTarget.toRingHom (maximalIdeal L)

namespace genericIdeal

/-- The generic-center ideal is prime. -/
instance isPrime (S : Algebra.DVR.Factorization R L) :
    S.genericIdeal.IsPrime := sorry

end genericIdeal

namespace closedIdeal

/-- The closed-center ideal is prime. -/
instance isPrime (S : Algebra.DVR.Factorization R L) :
    S.closedIdeal.IsPrime := sorry

end closedIdeal

/-- The prime-spectrum point defined by the generic center. -/
@[stacks 0BJ2 "generic center point"]
abbrev genericPoint (S : Algebra.DVR.Factorization R L) : PrimeSpectrum S.mid :=
  ⟨S.genericIdeal, inferInstance⟩

/-- The prime-spectrum point defined by the closed center. -/
@[stacks 0BJ2 "closed center point"]
abbrev closedPoint (S : Algebra.DVR.Factorization R L) : PrimeSpectrum S.mid :=
  ⟨S.closedIdeal, inferInstance⟩

/-- A flat finite-type algebra over the source DVR is finitely presented. -/
instance (S : Algebra.DVR.Factorization R L) :
    Algebra.FinitePresentation R S.mid := sorry

/-- Membership in the generic center means vanishing under the factorization map. -/
@[stacks 0BJ2 "generic center membership", simp]
theorem mem_genericIdeal_iff (S : Algebra.DVR.Factorization R L) {x : S.mid} :
    x ∈ S.genericIdeal ↔ S.toTarget x = 0 := sorry

/-- Membership in the closed center is detected by the target maximal ideal. -/
@[stacks 0BJ2 "closed center membership", simp]
theorem mem_closedIdeal_iff (S : Algebra.DVR.Factorization R L) {x : S.mid} :
    x ∈ S.closedIdeal ↔ S.toTarget x ∈ maximalIdeal L := sorry

/-- The image of the source maximal ideal is contained in the closed center. -/
theorem map_maximalIdeal_le_closedIdeal [IsExtensionOfDiscreteValuationRings R L]
    (S : Algebra.DVR.Factorization R L) :
    Ideal.map (algebraMap R S.mid) (maximalIdeal R) ≤ S.closedIdeal := sorry

/-- The generic center lies over the generic point of the source DVR. -/
@[simp]
theorem genericIdeal_under [IsExtensionOfDiscreteValuationRings R L]
    (S : Algebra.DVR.Factorization R L) :
    S.genericIdeal.under R = (⊥ : Ideal R) := sorry

/-- The closed center lies over the closed point of the source DVR. -/
@[simp]
theorem closedIdeal_under [IsExtensionOfDiscreteValuationRings R L]
    (S : Algebra.DVR.Factorization R L) :
    S.closedIdeal.under R = maximalIdeal R := sorry

/-- The generic center specializes to the closed center. -/
theorem genericIdeal_le_closedIdeal (S : Algebra.DVR.Factorization R L) :
    S.genericIdeal ≤ S.closedIdeal := sorry

/-- The generic and closed centers are distinct. -/
theorem genericIdeal_lt_closedIdeal [IsExtensionOfDiscreteValuationRings R L]
    (S : Algebra.DVR.Factorization R L) :
    S.genericIdeal < S.closedIdeal := sorry

end DVR.Factorization

end Algebra
