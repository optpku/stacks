/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.SerreQuotient
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Counit
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Exactness
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Abelian

/-!
# Fppf Serre localization and quasi-coherent coreflection

Locally quasi-coherent fppf modules with flat base change admit a Serre
localization by parasitic objects. Restriction to the étale site followed by
quasi-coherent coreflection descends to a functor from this localization to
quasi-coherent fppf modules.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.FppfModules.LQCohFbc

variable {S : Scheme.{u}}

/-- Parasitic objects of `FppfModules.LQCohFbc X`, obtained by restricting
`FppfModules.parasitic` along the inclusion into fppf modules. -/
abbrev parasitic (X : GroupoidsOver S) [AlgebraicStack X] :
    ObjectProperty (FppfModules.LQCohFbc X) :=
  (FppfModules.parasitic X).inverseImage (FppfModules.inclusion X)

/-- An object of `FppfModules.LQCohFbc X` is parasitic if and only if its
underlying fppf module is parasitic. -/
theorem parasitic_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    parasitic X F ↔ FppfModules.parasitic X ((FppfModules.inclusion X).obj F) :=
  sorry

/-- Membership in `parasitic X` is inverse image of `FppfModules.parasitic`
along `FppfModules.inclusion X`. -/
theorem mem_parasitic {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    parasitic X F ↔ FppfModules.parasitic X ((FppfModules.inclusion X).obj F) :=
  sorry

/-- Parasitic objects of `FppfModules.LQCohFbc X` form a Serre class. -/
instance parasitic_isSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    IsSerreClass (parasitic X) := sorry

/-- The Serre localization of locally quasi-coherent fppf modules with flat
base change by parasitic objects. -/
abbrev Quotient (X : GroupoidsOver S) [AlgebraicStack X] :=
  (parasitic X).isoModSerre.Localization

/-- `Quotient X` is the localization of `FppfModules.LQCohFbc X` at isomorphisms
modulo parasitic objects. -/
theorem Quotient_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    Quotient X = (parasitic X).isoModSerre.Localization := sorry

/-- The Serre quotient functor `Q : FppfModules.LQCohFbc X ⥤ Quotient X`. -/
def toQCoh (X : GroupoidsOver S) [AlgebraicStack X] :
    FppfModules.LQCohFbc X ⥤ Quotient X :=
  (parasitic X).isoModSerre.Q

/-- `toQCoh X` is the canonical localization functor at
`(parasitic X).isoModSerre`. -/
theorem toQCoh_eq (X : GroupoidsOver S) [AlgebraicStack X] :
    toQCoh X = (parasitic X).isoModSerre.Q := sorry

/-- The kernel of `toQCoh X` is exactly the parasitic objects of
`FppfModules.LQCohFbc X`. -/
theorem toQCoh_kernel (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.kernel (toQCoh X) = parasitic X := sorry

/-- An object of `FppfModules.LQCohFbc X` becomes zero after `toQCoh` if and
only if it is parasitic. -/
theorem toQCoh_isZero_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    IsZero ((toQCoh X).obj F) ↔ parasitic X F := sorry

/-- `toQCoh X` is an exact functor of abelian categories. -/
theorem toQCoh_exact (X : GroupoidsOver S) [AlgebraicStack X] :
    exactFunctor (FppfModules.LQCohFbc X) (Quotient X) (toQCoh X) := sorry

/-- Restriction from locally quasi-coherent fppf modules with flat base change
to locally quasi-coherent étale modules with flat base change. -/
def restrictionFunctor (X : GroupoidsOver S) [AlgebraicStack X] :
    FppfModules.LQCohFbc X ⥤ GroupoidsOver.LQCohFbc X :=
  (GroupoidsOver.lqcohFbc X).lift
    (FppfModules.inclusion X ⋙ GroupoidsOver.restriction X)
    (fun F ↦ F.property)

/-- The quasi-coherent coreflector on locally quasi-coherent fppf modules with
flat base change, obtained by étale restriction and quasi-coherent coreflection. -/
def coreflector (X : GroupoidsOver S) [AlgebraicStack X] :
    FppfModules.LQCohFbc X ⥤ GroupoidsOver.QCoh X :=
  restrictionFunctor X ⋙ GroupoidsOver.LQCohFbc.toQCoh X

/-- The fppf quasi-coherent coreflector preserves finite limits and finite colimits. -/
theorem coreflector_exact (X : GroupoidsOver S) [AlgebraicStack X] :
    exactFunctor (FppfModules.LQCohFbc X) (GroupoidsOver.QCoh X)
      (coreflector X) := sorry

/-- The kernel of the fppf quasi-coherent coreflector consists exactly of
parasitic objects. -/
theorem coreflector_kernel (X : GroupoidsOver S) [AlgebraicStack X] :
    Functor.kernel (coreflector X) = parasitic X := sorry

/-- The fppf quasi-coherent coreflector inverts morphisms that are isomorphisms
modulo parasitic objects. -/
theorem coreflector_inverts_isoModSerre (X : GroupoidsOver S) [AlgebraicStack X] :
    (parasitic X).isoModSerre.IsInvertedBy (coreflector X) := sorry

/-- The functor from the Serre localization by parasitic objects to
quasi-coherent fppf modules induced by quasi-coherent coreflection. -/
def quotientToQCoh (X : GroupoidsOver S) [AlgebraicStack X] :
    Quotient X ⥤ GroupoidsOver.QCoh X :=
  Localization.Construction.lift (coreflector X) (coreflector_inverts_isoModSerre X)

/-- Localization followed by its induced quasi-coherent comparison is
canonically isomorphic to the fppf quasi-coherent coreflector. -/
def toQCoh_comp_quotientToQCoh (X : GroupoidsOver S) [AlgebraicStack X] :
    toQCoh X ⋙ quotientToQCoh X ≅ coreflector X :=
  eqToIso (Localization.Construction.fac (coreflector X)
    (coreflector_inverts_isoModSerre X))

/-- The functor from the parasitic Serre localization to quasi-coherent fppf
modules preserves finite limits and finite colimits. -/
theorem quotientToQCoh_exact (X : GroupoidsOver S) [AlgebraicStack X] :
    exactFunctor (Quotient X) (GroupoidsOver.QCoh X) (quotientToQCoh X) := sorry

/-- An object of the parasitic Serre localization is zero if and only if its
image as a quasi-coherent fppf module is zero. -/
theorem quotientToQCoh_isZero_iff {X : GroupoidsOver S} [AlgebraicStack X]
    (F : Quotient X) :
    IsZero ((quotientToQCoh X).obj F) ↔ IsZero F := sorry

end AlgebraicGeometry.GroupoidsOver.FppfModules.LQCohFbc
