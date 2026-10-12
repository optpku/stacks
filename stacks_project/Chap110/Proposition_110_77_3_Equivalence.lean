/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.SimpleModule.Basic
public import ReasLib.CategoryTheory.Abelian.SerreQuotient
public import stacks_project.Chap110.Proposition_110_77_1_Equivalence
public import stacks_project.Chap110.Proposition_110_77_3_Torsion

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

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Small.{v} R]

/-- The fraction field of a small ring remains small, via the surjection from pairs
`(r, s)` onto `Localization (nonZeroDivisors R)`. -/
instance instSmallFractionRing : Small.{v} (FractionRing R) :=
  small_of_surjective Localization.mkHom_surjective

/-- Localization at the non-zero-divisors preserves finite generation. -/
theorem localizedModule_finite (M : FGModuleCat.{v} R) :
    ModuleCat.isFG.{v} (FractionRing R)
      ((forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R) ⋙
        ModuleCat.localizedModuleFunctor.{v} (nonZeroDivisors R)).obj M) :=
  sorry

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

/-- A field is a Noetherian ring, so the fraction field of a domain is Noetherian. -/
instance instIsNoetherianRingFractionRing : IsNoetherianRing (FractionRing R) :=
  inferInstance

/-- The inclusion of finitely generated modules over the fraction field preserves finite
limits. -/
instance instPreservesFiniteLimitsIsFGι :
    PreservesFiniteLimits (ModuleCat.isFG.{v} (FractionRing R)).ι :=
  inferInstanceAs
    (PreservesFiniteLimits
      (forget₂ (FGModuleCat.{v} (FractionRing R)) (ModuleCat.{v} (FractionRing R))))

/-- The inclusion of finitely generated modules over the fraction field preserves finite
colimits. -/
instance instPreservesFiniteColimitsIsFGι :
    PreservesFiniteColimits (ModuleCat.isFG.{v} (FractionRing R)).ι :=
  inferInstanceAs
    (PreservesFiniteColimits
      (forget₂ (FGModuleCat.{v} (FractionRing R)) (ModuleCat.{v} (FractionRing R))))

/-- The inclusion of finitely generated modules over the fraction field reflects finite
limits. -/
instance instReflectsFiniteLimitsIsFGι :
    ReflectsFiniteLimits (ModuleCat.isFG.{v} (FractionRing R)).ι :=
  reflectsFiniteLimits_of_reflectsIsomorphisms _

/-- The inclusion of finitely generated modules over the fraction field reflects finite
colimits. -/
instance instReflectsFiniteColimitsIsFGι :
    ReflectsFiniteColimits (ModuleCat.isFG.{v} (FractionRing R)).ι :=
  reflectsFiniteColimitsOfReflectsIsomorphisms _

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

/-- The underlying functor of `localizedExactFunctor` is localization of finitely generated
modules. -/
theorem localizedExactFunctor_obj :
    (localizedExactFunctor.obj :
      FGModuleCat.{v} R ⥤ FGModuleCat.{v} (FractionRing R)) =
      localizedModuleFunctor :=
  sorry

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

/-- The factorization isomorphism is inverted by its inverse. -/
theorem inducedLocalizedFunctor_fac_hom_inv_id :
    inducedLocalizedFunctor_fac.hom ≫ inducedLocalizedFunctor_fac.inv =
      𝟙 ((isTorsion : ObjectProperty (FGModuleCat.{v} R)).isoModSerre.Q ⋙
        inducedLocalizedFunctor) :=
  sorry

end FGModuleCat

