/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
public import ReasLib.AlgebraicGeometry.RingedSite.Hom.BoundedCohomologyBasis
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pullback.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.CategoryTheory.Sites.BoundedCohomologyBasis
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Functor.Exact.Plus
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-below derived functors on module cohomology-in subcategories

The coefficient parameter is free, while the actual module level is the
canonical `max z v` used by ringed-site module categories and cohomology bases.
All restricted functors are full-subcategory restrictions; bounded bases and
unit conditions remain explicit inputs to the landing theorems.
-/

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty

noncomputable section

-- Local instance justification (defeq pin): the generic ringed-site ModuleCat derived owner is
-- required by the derived-category APIs in this presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

universe wι z u v w

namespace RingedSite.Hom

/-- The bounded-below derived module property with cohomology in `A`. -/
@[stacks 06UQ "bounded-below module cohomology-in property"]
abbrev modulePlusCohomologyIn
    (X : RingedSite.{u, v, w}) [UnivLE.{max u v, max z v}]
    (A : ObjectProperty (ModuleCat.{max z v} X)) :
    ObjectProperty (DerivedCategory.Plus (ModuleCat.{max z v} X)) :=
  DerivedCategory.Plus.cohomologyIn A

/-- The bounded-below derived full subcategory cut out by module cohomology
in `A`. -/
@[stacks 06UQ "bounded-below module cohomology-in full subcategory"]
abbrev ModulePlusCohomologyIn
    (X : RingedSite.{u, v, w}) [UnivLE.{max u v, max z v}]
    (A : ObjectProperty (ModuleCat.{max z v} X)) :=
  (modulePlusCohomologyIn X A).FullSubcategory

namespace moduleDerivedCohomologyIn.Plus

variable {X Y : RingedSite.{u, v, w}}
variable (f : RingedSite.Hom X Y)
variable [UnivLE.{max u v, max z v}]
variable [(f.modulePushforward.{max z v}).IsRightAdjoint]
variable [IsFlat.{max z v} f]
variable (A' : ObjectProperty (ModuleCat.{max z v} Y))
variable (A : ObjectProperty (ModuleCat.{max z v} X))

/-- The underived module pullback restricted to the selected object
properties. -/
@[stacks 0D7V "bounded-below module pullback restriction"]
noncomputable abbrev pullback
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z v})) :
    A'.FullSubcategory ⥤ A.FullSubcategory :=
  ObjectProperty.FullSubcategory.restrict
    (f.modulePullback.{max z v}) hpull

/-- Flat pullback maps the bounded-below cohomology-in property into the
source property. -/
@[stacks 0D7V "flat bounded-below pullback landing"]
theorem mapsPullbackDerived
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z v})) :
    modulePlusCohomologyIn Y A' ≤
      (modulePlusCohomologyIn X A).inverseImage
        (modulePullbackDerivedPlus.{max z v} f) := sorry

/-- The bounded-below derived pullback restricted to cohomology-in objects. -/
@[stacks 0D7V "bounded-below derived pullback restriction"]
noncomputable abbrev pullbackDerived
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z v})) :
    ModulePlusCohomologyIn Y A' ⥤ ModulePlusCohomologyIn X A :=
  ObjectProperty.FullSubcategory.restrict
    (modulePullbackDerivedPlus.{max z v} f)
    (mapsPullbackDerived (f := f) (A' := A') (A := A) hpull)

section Basis

variable [IsWeakSerreClass A'] [IsWeakSerreClass A]
variable [HasSheafify X.siteTopology AddCommGrpCat.{max z v}]
variable [HasExt.{max z v} (Sheaf X.siteTopology AddCommGrpCat.{max z v})]
variable [HasSheafify Y.siteTopology AddCommGrpCat.{max z v}]
variable [HasExt.{max z v} (Sheaf Y.siteTopology AddCommGrpCat.{max z v})]
variable [Functor.HasRightDerivedFunctor
  (f.modulePushforward.{max z v}).toBoundedBelowDerived
  (HomotopyCategory.Plus.quasiIso (ModuleCat.{max z v} X))]
variable (adj : modulePullbackDerivedPlus.{max z v} f ⊣
  modulePushforwardDerivedPlus.{max z v} f)

/-- Bounded cohomology bases and the degree-zero unit criterion make bounded-
below derived pushforward land in the target cohomology-in subcategory. -/
@[stacks 0D7V "bounded-below pushforward landing"]
theorem mapsPushforwardDerived
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z v}))
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      Y.structureSheaf A')
    (hunit : ∀ F' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max z v} Y) (0 : ℤ)).obj F'.obj))) :
    modulePlusCohomologyIn X A ≤
      (modulePlusCohomologyIn Y A').inverseImage
        (modulePushforwardDerivedPlus.{max z v} f) := sorry

/-- The bounded-below derived pushforward restricted to cohomology-in
objects. -/
@[stacks 0D7V "bounded-below derived pushforward restriction"]
noncomputable abbrev pushforwardDerived
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z v}))
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      Y.structureSheaf A')
    (hunit : ∀ F' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max z v} Y) (0 : ℤ)).obj F'.obj))) :
    ModulePlusCohomologyIn X A ⥤ ModulePlusCohomologyIn Y A' :=
  ObjectProperty.FullSubcategory.restrict
    (modulePushforwardDerivedPlus.{max z v} f)
    (mapsPushforwardDerived (f := f) (A' := A') (A := A)
      (hpull := hpull) (adj := adj) basisX basisY hunit)

/-- The adjunction between the two restricted bounded-below derived functors. -/
@[stacks 0D7V "bounded-below restricted pullback-pushforward adjunction"]
noncomputable def adjunction
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z v}))
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      Y.structureSheaf A')
    (hunit : ∀ F' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max z v} Y) (0 : ℤ)).obj F'.obj))) :
    pullbackDerived (f := f) (A' := A') (A := A) hpull ⊣
      pushforwardDerived (f := f) (A' := A') (A := A)
        (hpull := hpull) (adj := adj) basisX basisY hunit :=
  ObjectProperty.FullSubcategory.adjunction
    (modulePullbackDerivedPlus.{max z v} f)
    (modulePushforwardDerivedPlus.{max z v} f) adj
    (mapsPullbackDerived (f := f) (A' := A') (A := A) hpull)
    (mapsPushforwardDerived (f := f) (A' := A') (A := A)
      (hpull := hpull) (adj := adj) basisX basisY hunit)

/-- The restricted unit is invertible on every bounded-below cohomology-in
object under the basis hypotheses. -/
@[stacks 0D7V "bounded-below restricted unit criterion"]
theorem unit_isIso
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z v}))
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      Y.structureSheaf A')
    (hunit : ∀ F' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max z v} Y) (0 : ℤ)).obj F'.obj)))
    (K : ModulePlusCohomologyIn Y A') :
    IsIso ((adjunction (f := f) (A' := A') (A := A)
      (hpull := hpull) (adj := adj) basisX basisY hunit).unit.app K) := sorry

/-- The restricted counit is invertible on every bounded-below cohomology-in
object under the basis hypotheses. -/
@[stacks 0D7V "bounded-below restricted counit criterion"]
theorem counit_isIso
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z v}))
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      Y.structureSheaf A')
    (hunit : ∀ F' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max z v} Y) (0 : ℤ)).obj F'.obj)))
    (K : ModulePlusCohomologyIn X A) :
    IsIso ((adjunction (f := f) (A' := A') (A := A)
      (hpull := hpull) (adj := adj) basisX basisY hunit).counit.app K) := sorry

/-- The restricted bounded-below pullback is an equivalence under the bounded
cohomology-basis hypotheses. -/
@[stacks 0D7U "bounded-below cohomology-in pullback equivalence"]
theorem pullback_isEquivalence
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z v}))
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      X.structureSheaf A)
    (basisY : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      Y.structureSheaf A')
    (hunit : ∀ F' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max z v} Y) (0 : ℤ)).obj F'.obj))) :
    Functor.IsEquivalence
      (pullbackDerived (f := f) (A' := A') (A := A) hpull) := sorry

end Basis

section PullbackBasis

variable [IsWeakSerreClass A'] [IsWeakSerreClass A]
variable [HasSheafify X.siteTopology AddCommGrpCat.{max z v}]
variable [HasExt.{max z v} (Sheaf X.siteTopology AddCommGrpCat.{max z v})]
variable [Functor.HasRightDerivedFunctor
  (f.modulePushforward.{max z v}).toBoundedBelowDerived
  (HomotopyCategory.Plus.quasiIso (ModuleCat.{max z v} X))]
variable (adj : modulePullbackDerivedPlus.{max z v} f ⊣
  modulePushforwardDerivedPlus.{max z v} f)

/-- A pullback bounded basis suffices for bounded-below pushforward landing. -/
@[stacks 0D7W "bounded-below pullback-basis pushforward landing"]
theorem mapsPushforwardDerived_of_pullbackBasis
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z v}))
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      X.structureSheaf A)
    (basisf : PullbackBasis f A)
    (hunit : ∀ F' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max z v} Y) (0 : ℤ)).obj F'.obj))) :
    modulePlusCohomologyIn X A ≤
      (modulePlusCohomologyIn Y A').inverseImage
        (modulePushforwardDerivedPlus.{max z v} f) := sorry

/-- The bounded-below derived pushforward restricted using a pullback basis. -/
@[stacks 0D7W "bounded-below pullback-basis pushforward restriction"]
noncomputable abbrev pushforwardDerived_of_pullbackBasis
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z v}))
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      X.structureSheaf A)
    (basisf : PullbackBasis f A)
    (hunit : ∀ F' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max z v} Y) (0 : ℤ)).obj F'.obj))) :
    ModulePlusCohomologyIn X A ⥤ ModulePlusCohomologyIn Y A' :=
  ObjectProperty.FullSubcategory.restrict
    (modulePushforwardDerivedPlus.{max z v} f)
    (mapsPushforwardDerived_of_pullbackBasis (f := f) (A' := A') (A := A)
      (hpull := hpull) (adj := adj) basisX basisf hunit)

/-- A pullback bounded basis gives the bounded-below derived equivalence. -/
@[stacks 0D7W "bounded-below pullback-basis equivalence"]
theorem pullback_isEquivalence_of_pullbackBasis
    (hpull : A' ≤ A.inverseImage (f.modulePullback.{max z v}))
    [Functor.IsEquivalence (pullback f A' A hpull)]
    (basisX : CategoryTheory.GrothendieckTopology.BoundedCohomologyBasis
      X.structureSheaf A)
    (basisf : PullbackBasis f A)
    (hunit : ∀ F' : A'.FullSubcategory,
      IsIso (adj.unit.app
        ((DerivedCategory.Plus.singleFunctor (ModuleCat.{max z v} Y) (0 : ℤ)).obj F'.obj))) :
    Functor.IsEquivalence
      (pullbackDerived (f := f) (A' := A') (A := A) hpull) := sorry

end PullbackBasis

end moduleDerivedCohomologyIn.Plus

end RingedSite.Hom

end
