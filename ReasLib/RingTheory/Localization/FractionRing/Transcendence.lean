/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import ReasLib.RingTheory.Localization.FractionRing.Algebra
public import ReasLib.FieldTheory.Transcendence.FiniteType
public import ReasLib.RingTheory.Algebra.Tower

@[expose] public section

/-!
# Transcendence degree of fraction-ring extensions

This file packages the transcendence degree of the fraction fields of an injective map of
domains. The primary invariant remains `Cardinal`-valued; the natural-number view is only a
source-facing truncation for finite-type dimension formulas.
-/

namespace FractionRing

universe u v w

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Algebra R S]

/-- The cardinal-valued transcendence degree of the extension `Frac(R) → Frac(S)`.

The fraction-field algebra structure is deliberately local to this definition: mathlib does not
register `FractionRing.liftAlgebra` globally because it can create instance diamonds. -/
@[stacks 02IJ "fraction-ring transcendence degree"]
noncomputable def trdeg [FaithfulSMul R S] : Cardinal :=
  -- Local instance justification (instance diamond): the induced fraction-field algebra is
  -- canonical for this construction but intentionally not registered globally by mathlib.
  letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R (FractionRing S)
  Algebra.trdeg (FractionRing R) (FractionRing S)

/-- The natural-number view of `FractionRing.trdeg`.

This is a truncation of the cardinal-valued invariant, so it is intended for results that already
have a finite transcendence-degree hypothesis. It is `0` when the cardinal-valued degree is
infinite. -/
@[stacks 02IJ "natural fraction-ring transcendence degree"]
noncomputable def trdegNat [FaithfulSMul R S] : ℕ :=
  Cardinal.toNat (trdeg (R := R) (S := S))

/-- Passing from a faithful extension of domains to its fraction fields preserves the
cardinal-valued transcendence degree. -/
@[stacks 02IJ "fraction-ring transcendence degree transport"]
theorem trdeg_eq [FaithfulSMul R S] :
    trdeg (R := R) (S := S) = Algebra.trdeg R S := sorry

/-- Passing from a faithful extension of domains to its fraction fields preserves the
natural-number transcendence degree. -/
@[stacks 02IJ "natural fraction-ring transcendence degree transport"]
theorem trdegNat_eq [FaithfulSMul R S] :
    trdegNat (R := R) (S := S) = Cardinal.toNat (Algebra.trdeg R S) := sorry

/-- The cardinal-valued fraction-ring transcendence degree constructed from an injective algebra
map of domains. -/
@[stacks 02IJ "injective fraction-ring transcendence degree"]
noncomputable def trdegOf (hinj : Function.Injective (algebraMap R S)) : Cardinal :=
  -- Local instance justification (instance diamond): use the named induced fraction algebra only
  -- inside this definition, never as an ambient instance.
  letI : Algebra (FractionRing R) (FractionRing S) := algebraOfInjective (R := R) (S := S) hinj
  Algebra.trdeg (FractionRing R) (FractionRing S)

/-- The natural-number fraction-ring transcendence degree associated to an injective map of
domains. This is the `Cardinal.toNat` view, not the primary invariant. -/
@[stacks 02IJ "natural injective fraction-ring transcendence degree"]
noncomputable def trdegNatOf (hinj : Function.Injective (algebraMap R S)) : ℕ :=
  Cardinal.toNat (trdegOf (R := R) (S := S) hinj)

/-- The fraction-field transcendence degree formed from an explicit injectivity witness agrees
with the transcendence degree of the original algebra map. -/
@[stacks 02IJ "injective fraction-ring transcendence degree transport"]
theorem trdegOf_eq (hinj : Function.Injective (algebraMap R S)) :
    trdegOf (R := R) (S := S) hinj = Algebra.trdeg R S := sorry

/-- The natural-number fraction-field transcendence degree formed from an explicit injectivity
witness agrees with the natural-number transcendence degree of the original algebra map. -/
@[stacks 02IJ "natural injective fraction-ring transcendence degree transport"]
theorem trdegNatOf_eq (hinj : Function.Injective (algebraMap R S)) :
    trdegNatOf (R := R) (S := S) hinj = Cardinal.toNat (Algebra.trdeg R S) := sorry

section Tower

variable {R : Type u} {T : Type v} {U : Type w}
variable [CommRing R] [IsDomain R]
variable [CommRing T] [CommRing U] [IsDomain T] [IsDomain U]
variable [Algebra R T] [Algebra T U] [Algebra R U] [IsScalarTower R T U]
variable [Algebra.FiniteType R T] [Algebra.FiniteType T U]

/-- The natural-number fraction-field transcendence degrees of an injective finite-type tower of
domains add. The individual fraction-field algebra structures remain encapsulated by
`trdegNatOf`, so this theorem does not create a global instance diamond. -/
@[stacks 02IJ "fraction-ring transcendence degree tower"]
theorem trdegNatOf_tower
    (hinjRT : Function.Injective (algebraMap R T))
    (hinjTU : Function.Injective (algebraMap T U)) :
    trdegNatOf (R := R) (S := U)
        (IsScalarTower.algebraMap_injective_of_injective
          (R := R) (S := T) (A := U) hinjRT hinjTU) =
        trdegNatOf (R := R) (S := T) hinjRT +
        trdegNatOf (R := T) (S := U) hinjTU := sorry

end Tower

end FractionRing
