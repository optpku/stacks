/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SimpleModule.Basic
public import ReasLib.CategoryTheory.Abelian.SerreQuotient
public import ReasLib.Algebra.Category.FGModuleCat.Torsion

/-!
# Localization of finitely generated modules at the fraction field

The exact localization functor `FGModuleCat R ⥤ FGModuleCat (FractionRing R)`
descends uniquely through the Serre quotient by finitely generated torsion modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace FGModuleCat

variable {R : Type u} [CommRing R] [Small.{v} R]

/-- The fraction field of a small ring remains small, via the surjection from pairs
`(r, s)` onto `Localization (nonZeroDivisors R)`. -/
instance instSmallFractionRing : Small.{v} (FractionRing R) :=
  small_of_surjective Localization.mkHom_surjective

variable [IsDomain R] [IsNoetherianRing R]

/-- Localization at the non-zero-divisors preserves finite generation. -/
theorem localizedModule_finite (M : FGModuleCat.{v} R) :
    ModuleCat.isFG.{v} (FractionRing R)
      ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ⋙
        ModuleCat.localizedModuleFunctor.{v} (nonZeroDivisors R)).obj M) :=
  sorry

/-- Localization of a finitely generated module has a canonical finite-generation
instance over the fraction field. -/
instance instFiniteLocalizedModule (M : FGModuleCat.{v} R) :
    Module.Finite (FractionRing R)
      ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ⋙
        ModuleCat.localizedModuleFunctor.{v} (nonZeroDivisors R)).obj M) :=
  localizedModule_finite M

/-- Localization of finitely generated modules at the non-zero-divisors, landing in
finitely generated modules over the fraction field. -/
def localizedModuleFunctor :
    FGModuleCat.{v} R ⥤ FGModuleCat.{v} (FractionRing R) :=
  (ModuleCat.isFG.{v} (FractionRing R)).lift
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ⋙
      ModuleCat.localizedModuleFunctor.{v} (nonZeroDivisors R))
    localizedModule_finite

/-- Localization of modules, restricted from finitely generated `R`-modules, preserves
finite limits. -/
instance instPreservesFiniteLimitsLocalizedModuleFunctorUnderlying :
    PreservesFiniteLimits
      (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ⋙
        ModuleCat.localizedModuleFunctor.{v} (nonZeroDivisors R)) :=
  comp_preservesFiniteLimits
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R))
    (ModuleCat.localizedModuleFunctor.{v} (nonZeroDivisors R))

/-- Localization of modules, restricted from finitely generated `R`-modules, preserves
finite colimits. -/
instance instPreservesFiniteColimitsLocalizedModuleFunctorUnderlying :
    PreservesFiniteColimits
      (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ⋙
        ModuleCat.localizedModuleFunctor.{v} (nonZeroDivisors R)) :=
  comp_preservesFiniteColimits
    (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R))
    (ModuleCat.localizedModuleFunctor.{v} (nonZeroDivisors R))

/-- After composing with the inclusion of finitely generated modules over the fraction
field, localization preserves finite limits. -/
instance instPreservesFiniteLimitsLocalizedModuleFunctorCompι :
    PreservesFiniteLimits
      (localizedModuleFunctor ⋙ (ModuleCat.isFG.{v} (FractionRing R)).ι) :=
  preservesFiniteLimits_of_natIso
    ((ModuleCat.isFG.{v} (FractionRing R)).liftCompιIso
      (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ⋙
        ModuleCat.localizedModuleFunctor.{v} (nonZeroDivisors R))
      localizedModule_finite).symm

/-- After composing with the inclusion of finitely generated modules over the fraction
field, localization preserves finite colimits. -/
instance instPreservesFiniteColimitsLocalizedModuleFunctorCompι :
    PreservesFiniteColimits
      (localizedModuleFunctor ⋙ (ModuleCat.isFG.{v} (FractionRing R)).ι) :=
  preservesFiniteColimits_of_natIso
    ((ModuleCat.isFG.{v} (FractionRing R)).liftCompιIso
      (forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ⋙
        ModuleCat.localizedModuleFunctor.{v} (nonZeroDivisors R))
      localizedModule_finite).symm

/-- Localization of finitely generated modules preserves finite limits, because the
inclusion into `ModuleCat` creates and reflects them. -/
instance instPreservesFiniteLimitsLocalizedModuleFunctor :
    PreservesFiniteLimits
      (localizedModuleFunctor : FGModuleCat.{v} R ⥤ FGModuleCat.{v} (FractionRing R)) :=
  preservesFiniteLimits_of_reflects_of_preserves
    (localizedModuleFunctor : FGModuleCat.{v} R ⥤ FGModuleCat.{v} (FractionRing R))
    (ModuleCat.isFG.{v} (FractionRing R)).ι

/-- Localization of finitely generated modules preserves finite colimits, because the
inclusion into `ModuleCat` creates and reflects them. -/
instance instPreservesFiniteColimitsLocalizedModuleFunctor :
    PreservesFiniteColimits
      (localizedModuleFunctor : FGModuleCat.{v} R ⥤ FGModuleCat.{v} (FractionRing R)) :=
  preservesFiniteColimits_of_reflects_of_preserves
    (localizedModuleFunctor : FGModuleCat.{v} R ⥤ FGModuleCat.{v} (FractionRing R))
    (ModuleCat.isFG.{v} (FractionRing R)).ι

/-- Localization of finitely generated modules, bundled as an exact functor. -/
def localizedExactFunctor :
    FGModuleCat.{v} R ⥤ₑ FGModuleCat.{v} (FractionRing R) :=
  ExactFunctor.of
    (localizedModuleFunctor : FGModuleCat.{v} R ⥤ FGModuleCat.{v} (FractionRing R))

/-- Finitely generated torsion modules are sent to zero by localization at the fraction
field. -/
theorem isTorsion_le_localizedExactFunctor_kernel :
    (isTorsion : ObjectProperty (FGModuleCat.{v} R)) ≤
      (localizedExactFunctor.obj :
        FGModuleCat.{v} R ⥤ FGModuleCat.{v} (FractionRing R)).kernel :=
  sorry

/-- The exact functor induced on the Serre quotient of finitely generated torsion modules
by localization at the fraction field. -/
def inducedLocalizedFunctor :
    (isTorsion : ObjectProperty (FGModuleCat.{v} R)).isoModSerre.Localization ⥤
      FGModuleCat.{v} (FractionRing R) :=
  SerreClassLocalization.inducedFunctor
    (isTorsion : ObjectProperty (FGModuleCat.{v} R)) localizedExactFunctor
    isTorsion_le_localizedExactFunctor_kernel

/-- The Serre quotient followed by the induced functor recovers localization of finitely
generated modules. -/
def inducedLocalizedFunctor_fac :
    (isTorsion : ObjectProperty (FGModuleCat.{v} R)).isoModSerre.Q ⋙
        inducedLocalizedFunctor ≅
      localizedModuleFunctor :=
  CategoryTheory.Localization.fac
    (localizedExactFunctor.obj :
      FGModuleCat.{v} R ⥤ FGModuleCat.{v} (FractionRing R))
    (((isTorsion : ObjectProperty (FGModuleCat.{v} R)).isoModSerre_isInvertedBy_iff
      (localizedExactFunctor.obj :
        FGModuleCat.{v} R ⥤ FGModuleCat.{v} (FractionRing R))).2
      isTorsion_le_localizedExactFunctor_kernel)
    (isTorsion : ObjectProperty (FGModuleCat.{v} R)).isoModSerre.Q

/-- For a Noetherian integral domain, localization at the non-zero-divisors induces
an equivalence from the Serre quotient of finitely generated modules by torsion modules
to finite-dimensional vector spaces over the fraction field. -/
theorem inducedLocalizedFunctor_isEquivalence :
    (inducedLocalizedFunctor :
      isTorsion.isoModSerre.Localization ⥤
        FGModuleCat.{v} (FractionRing R)).IsEquivalence :=
  sorry

/-- The functor induced by localization on the torsion Serre quotient is canonically
an equivalence. -/
instance instIsEquivalenceInducedLocalizedFunctor :
    (inducedLocalizedFunctor :
      isTorsion.isoModSerre.Localization ⥤
        FGModuleCat.{v} (FractionRing R)).IsEquivalence :=
  inducedLocalizedFunctor_isEquivalence

end FGModuleCat
