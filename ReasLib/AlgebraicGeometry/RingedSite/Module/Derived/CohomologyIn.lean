/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Hom.BoundedCohomologyBasis
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Flat
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.BoundedCohomology
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Structure
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Derived pullback and pushforward on cohomology-in subcategories

This leaf owns the restricted derived functors used by the localization arguments in Chapter 21.
The coefficient universe is independent of the site universes.  The adjunction is an explicit
input, so a proof of an absolute derived comparison never silently chooses observable unit or
counit data through a local instance.
-/

open CategoryTheory CategoryTheory.Limits
-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
open CategoryTheory.ObjectProperty
open DerivedCategory

noncomputable section

universe q u v w

namespace RingedSite.Hom

/-- The canonical cohomology-in property on the derived category of module sheaves. -/
@[stacks 06UQ "module derived objects with cohomology in an object property"]
abbrev moduleCohomologyIn
    (X : RingedSite.{u, v, w}) [UnivLE.{max u v, q}]
    (A : ObjectProperty (ModuleCat.{q} X)) :
    ObjectProperty (ModuleDerived.{q} X) :=
  @DerivedCategory.cohomologyIn _ _ _ (moduleCat_hasDerivedCategory X) A

/-- The full subcategory of derived module objects with cohomology in `A`. -/
@[stacks 06UQ "module cohomology-in full subcategory"]
abbrev ModuleCohomologyIn
    (X : RingedSite.{u, v, w}) [UnivLE.{max u v, q}]
    (A : ObjectProperty (ModuleCat.{q} X)) :=
  (moduleCohomologyIn X A).FullSubcategory

end RingedSite.Hom

universe wι z uX vX uY vY

namespace RingedSite.Hom.moduleDerivedCohomologyIn

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
variable (f : RingedSite.Hom X Y)

-- Both site universes and the coefficient universe remain independent.  The common coefficient
-- level is the least symmetric level at which module categories over `X` and `Y` can be compared.
variable [UnivLE.{max uX vX, max z vX vY}]
variable [UnivLE.{max uY vY, max z vX vY}]
variable [(f.modulePushforward.{max z vX vY}).IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{max z vX vY} f)
    (ModuleQis.{max z vX vY} X)]
variable [Functor.HasLeftDerivedFunctor
  (modulePullbackToDerived.{max z vX vY} f)
    (ModuleQis.{max z vX vY} Y)]

section WeakSerre

variable (A' : ObjectProperty (ModuleCat.{max z vX vY} Y))
variable (A : ObjectProperty (ModuleCat.{max z vX vY} X))

/-- The module pullback restricted to full subcategories selected by object properties. -/
@[stacks 0D7V "pullback on module full subcategories"]
noncomputable abbrev pullback
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z vX vY})) :
    A'.FullSubcategory ⥤ A.FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict
    (f.modulePullback.{max z vX vY}) hpull

end WeakSerre

section Derived

variable (A' : ObjectProperty (ModuleCat.{max z vX vY} Y))
variable (A : ObjectProperty (ModuleCat.{max z vX vY} X))
variable [HasSheafify X.siteTopology AddCommGrpCat.{max z vX vY}]
variable [HasExt.{max z vX vY}
  (Sheaf X.siteTopology AddCommGrpCat.{max z vX vY})]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max z vX vY}]
variable [HasExt.{max z vX vY}
  (Sheaf Y.siteTopology AddCommGrpCat.{max z vX vY})]
variable [IsFlat.{max z vX vY} f]

/-- Exact flat pullback maps the target cohomology-in property into the source property. -/
@[stacks 0D7V "flat pullback preserves cohomology-in objects"]
theorem mapsPullbackDerived
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z vX vY})) :
    moduleCohomologyIn.{max z vX vY} Y A' ≤
      (moduleCohomologyIn.{max z vX vY} X A).inverseImage
        (modulePullbackDerived.{max z vX vY} f) := sorry

/-- The derived pullback restricted canonically to cohomology-in subcategories. -/
@[stacks 0D7V "derived pullback on cohomology-in subcategories"]
noncomputable abbrev pullbackDerived
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z vX vY})) :
    ModuleCohomologyIn.{max z vX vY} Y A' ⥤
      ModuleCohomologyIn.{max z vX vY} X A :=
  ObjectProperty.FullSubcategory.restrict
    (modulePullbackDerived.{max z vX vY} f)
    (mapsPullbackDerived (f := f) (A' := A') (A := A) hpull)

variable [IsWeakSerreClass A'] [IsWeakSerreClass A]
variable (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z vX vY}))
variable (adj : modulePullbackDerived.{max z vX vY} f ⊣
  modulePushforwardDerived.{max z vX vY} f)

/-- Bounded bases and the degree-zero unit condition make derived pushforward map the source
cohomology-in property into the target property. -/
@[stacks 0D7V "bounded-basis pushforward landing"]
theorem mapsPushforwardDerived
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vX, vY, uY}
      Y.structureSheaf A')
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max z vX vY} Y) (0 : ℤ)).obj ℱ'.obj))) :
    moduleCohomologyIn.{max z vX vY} X A ≤
      (moduleCohomologyIn.{max z vX vY} Y A').inverseImage
        (modulePushforwardDerived.{max z vX vY} f) := sorry

/-- The derived pushforward restricted canonically to cohomology-in subcategories. -/
@[stacks 0D7V "derived pushforward on cohomology-in subcategories"]
noncomputable abbrev pushforwardDerived
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vX, vY, uY}
      Y.structureSheaf A')
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max z vX vY} Y) (0 : ℤ)).obj ℱ'.obj))) :
    ModuleCohomologyIn.{max z vX vY} X A ⥤
      ModuleCohomologyIn.{max z vX vY} Y A' :=
  ObjectProperty.FullSubcategory.restrict
    (modulePushforwardDerived.{max z vX vY} f)
    (mapsPushforwardDerived (f := f) (A' := A') (A := A) (hpull := hpull)
      (adj := adj) basisX basisY hunit)

/-- The restricted derived pullback is an equivalence under bounded bases and the degree-zero unit
condition. -/
@[stacks 0D7V "equivalence on cohomology-in subcategories"]
theorem pullback_isEquivalence
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vX, vY, uY}
      Y.structureSheaf A')
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max z vX vY} Y) (0 : ℤ)).obj ℱ'.obj))) :
    Functor.IsEquivalence (pullbackDerived f A' A hpull) := sorry

end Derived

section PullbackBasis

variable (A' : ObjectProperty (ModuleCat.{max z vX vY} Y))
variable (A : ObjectProperty (ModuleCat.{max z vX vY} X))
variable [IsWeakSerreClass A'] [IsWeakSerreClass A]
variable (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z vX vY}))
variable [HasSheafify X.siteTopology AddCommGrpCat.{max z vX vY}]
variable [HasExt.{max z vX vY}
  (Sheaf X.siteTopology AddCommGrpCat.{max z vX vY})]
variable (adj : modulePullbackDerived.{max z vX vY} f ⊣
  modulePushforwardDerived.{max z vX vY} f)
variable [IsFlat.{max z vX vY} f]

/-- A pullback bounded basis makes derived pushforward map the source cohomology-in property into
the target property without requiring a target-site basis. -/
@[stacks 0D7W "pullback-basis pushforward landing"]
theorem mapsPushforwardDerived_of_pullbackBasis
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisf : RingedSite.Hom.PullbackBasis.{w, max z vY, uX, vX, uY, vY, wι} f A)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max z vX vY} Y) (0 : ℤ)).obj ℱ'.obj))) :
    moduleCohomologyIn.{max z vX vY} X A ≤
      (moduleCohomologyIn.{max z vX vY} Y A').inverseImage
        (modulePushforwardDerived.{max z vX vY} f) := sorry

/-- The restricted derived pushforward under a pullback bounded basis. -/
@[stacks 0D7W "pullback-basis derived pushforward restriction"]
noncomputable abbrev pushforwardDerived_of_pullbackBasis
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisf : RingedSite.Hom.PullbackBasis.{w, max z vY, uX, vX, uY, vY, wι} f A)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max z vX vY} Y) (0 : ℤ)).obj ℱ'.obj))) :
    ModuleCohomologyIn.{max z vX vY} X A ⥤
      ModuleCohomologyIn.{max z vX vY} Y A' :=
  ObjectProperty.FullSubcategory.restrict
    (modulePushforwardDerived.{max z vX vY} f)
    (mapsPushforwardDerived_of_pullbackBasis (f := f) (A' := A') (A := A)
      (hpull := hpull) (adj := adj) basisX basisf hunit)

/-- A pullback bounded basis gives the unit criterion on every cohomology-in object. -/
@[stacks 0D7W "pullback-basis derived unit criterion"]
theorem unit_isIso_of_pullbackBasis
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisf : RingedSite.Hom.PullbackBasis.{w, max z vY, uX, vX, uY, vY, wι} f A)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max z vX vY} Y) (0 : ℤ)).obj ℱ'.obj)))
    (K : ModuleCohomologyIn.{max z vX vY} Y A') :
    IsIso (adj.unit.app K.obj) := sorry

/-- A pullback bounded basis gives the counit criterion on every cohomology-in object. -/
@[stacks 0D7W "pullback-basis derived counit criterion"]
theorem counit_isIso_of_pullbackBasis
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisf : RingedSite.Hom.PullbackBasis.{w, max z vY, uX, vX, uY, vY, wι} f A)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max z vX vY} Y) (0 : ℤ)).obj ℱ'.obj)))
    (K : ModuleCohomologyIn.{max z vX vY} X A) :
    IsIso (adj.counit.app K.obj) := sorry

/-- Joint unit-and-counit form of the pullback-basis criterion. -/
@[stacks 0D7W "pullback-basis derived unit and counit criterion"]
theorem unitCounit_isIso_of_pullbackBasis
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisf : RingedSite.Hom.PullbackBasis.{w, max z vY, uX, vX, uY, vY, wι} f A)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max z vX vY} Y) (0 : ℤ)).obj ℱ'.obj))) :
    (∀ K : ModuleCohomologyIn.{max z vX vY} Y A', IsIso (adj.unit.app K.obj)) ∧
      (∀ K : ModuleCohomologyIn.{max z vX vY} X A, IsIso (adj.counit.app K.obj)) := sorry

/-- The restricted pullback is an equivalence under the local pullback-basis hypotheses. -/
@[stacks 0D7W "pullback-basis restricted pullback equivalence"]
theorem pullback_isEquivalence_of_pullbackBasis
    [Functor.IsEquivalence (pullback f A' A hpull)]
    [HasSheafify Y.siteTopology AddCommGrpCat.{max z vX vY}]
    [HasExt.{max z vX vY}
      (Sheaf Y.siteTopology AddCommGrpCat.{max z vX vY})]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis.{wι, w, max z vY, vX, uX}
      X.structureSheaf A)
    (basisf : RingedSite.Hom.PullbackBasis.{w, max z vY, uX, vX, uY, vY, wι} f A)
    (hunit : ∀ ℱ' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.singleFunctor (ModuleCat.{max z vX vY} Y) (0 : ℤ)).obj ℱ'.obj))) :
    Functor.IsEquivalence
      (pullbackDerived f A' A hpull :
        ModuleCohomologyIn.{max z vX vY} Y A' ⥤
          ModuleCohomologyIn.{max z vX vY} X A) := sorry

end PullbackBasis

end RingedSite.Hom.moduleDerivedCohomologyIn

end
