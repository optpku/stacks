/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.BaseChange
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived.GlobalSections
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change for derived global sections with support

This file constructs the pullback component on derived global sections with support from three
geometric inputs: ambient pullback on derived global sections, pullback on the closed-subset
derived categories, and the comparison of the two derived direct images.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.BaseChange

variable {X X' : RingedSpace.{u}}

/-- Ambient derived global sections after forgetting the module structure. -/
@[stacks 0G79 "underlying additive derived global sections"]
abbrev ambient (X : RingedSpace.{u}) :
    DerivedCategory X.Modules ⥤ DerivedCategory AddCommGrpCat.{u} :=
  Module.Derived.GlobalSections.functor X ⋙
    ModuleCat.forgetDerived (globalSectionsRing X)

/-- Derived global sections with support after forgetting the module structure. -/
@[stacks 0G79 "underlying additive derived global sections with support"]
abbrev supported (X : RingedSpace.{u}) (Z : Closeds X) :
    DerivedCategory X.Modules ⥤ DerivedCategory AddCommGrpCat.{u} :=
  GlobalSectionsWithSupport.derived X Z ⋙
    ModuleCat.forgetDerived (globalSectionsRing X)

/-- The ambient comparison model for additive derived global sections with support. -/
@[stacks 0G79 "ambient additive model for derived global sections with support"]
abbrev model (X : RingedSpace.{u}) (Z : Closeds X) :
    DerivedCategory X.Modules ⥤ DerivedCategory AddCommGrpCat.{u} :=
  GlobalSectionsWithSupport.ambientModel X Z ⋙
    ModuleCat.forgetDerived (globalSectionsRing X)

/-- The supported-to-ambient comparison after forgetting the module structure. -/
@[stacks 0G79 "ambient additive comparison for derived global sections with support"]
noncomputable abbrev comparison (X : RingedSpace.{u}) (Z : Closeds X) :
    supported X Z ⟶ model X Z :=
  Functor.whiskerRight (GlobalSectionsWithSupport.ambientComparison X Z)
    (ModuleCat.forgetDerived (globalSectionsRing X))

/-- The derived forget-support transformation after forgetting the module structure. -/
@[stacks 0G79 "underlying additive derived forget-support map"]
noncomputable def forget (X : RingedSpace.{u}) (Z : Closeds X) :
    supported X Z ⟶ ambient X :=
  Functor.whiskerRight (GlobalSectionsWithSupport.forgetDerived X Z)
    (ModuleCat.forgetDerived (globalSectionsRing X))

variable {f : X' ⟶ X} {Z : Closeds X} {Z' : Closeds X'}
variable {closedPullback : ModuleDerived X Z ⥤ ModuleDerived X' Z'}
variable (squareIso :
  closedPullback ⋙ Pushforward.derived X' Z' ≅
    Pushforward.derived X Z ⋙ modulePullbackDerived f)
variable (ambientPullback : ambient X ⟶ modulePullbackDerived f ⋙ ambient X')

/-- The canonical ambient-model component of pullback on derived global sections with support. -/
@[stacks 0G79 "ambient model of pullback on derived global sections with support"]
noncomputable def modelApp (K : DerivedCategory X.Modules) :
    (supported X Z).obj K ⟶
      (modulePullbackDerived f ⋙ model X' Z').obj K :=
  (comparison X Z).app K ≫
    ambientPullback.app
      ((Pushforward.derived X Z).obj ((SectionsWithSupport.derived X Z).obj K)) ≫
    (ambient X').map
      (squareIso.inv.app ((SectionsWithSupport.derived X Z).obj K) ≫
        (Pushforward.derived X' Z').map
          (DerivedBaseChange.app squareIso K))

/-- The ambient-model components of supported pullback are natural in the ambient derived
module. -/
@[stacks 0G79 "naturality of the ambient supported-pullback model"]
theorem modelApp_naturality {K L : DerivedCategory X.Modules} (g : K ⟶ L) :
    (supported X Z).map g ≫ modelApp squareIso ambientPullback L =
      modelApp squareIso ambientPullback K ≫
        (modulePullbackDerived f ⋙ model X' Z').map g := sorry

/-- Pullback on the ambient model for additive derived global sections with support. -/
@[stacks 0G79 "ambient model of pullback on derived global sections with support"]
noncomputable def modelMap :
    supported X Z ⟶ modulePullbackDerived f ⋙ model X' Z' where
  app K := modelApp squareIso ambientPullback K
  naturality _ _ g := modelApp_naturality squareIso ambientPullback g

/-- The target comparison from supported pullback to its ambient model. -/
@[stacks 0G79 "target ambient comparison for supported pullback"]
noncomputable abbrev targetComparison (f : X' ⟶ X) (Z' : Closeds X') :
    modulePullbackDerived f ⋙ supported X' Z' ⟶
      modulePullbackDerived f ⋙ model X' Z' :=
  Functor.whiskerLeft (modulePullbackDerived f) (comparison X' Z')

/-- Pullback on additive derived global sections with support, as a natural transformation. -/
@[stacks 0G79 "pullback on derived global sections with support"]
noncomputable def map :
    supported X Z ⟶ modulePullbackDerived f ⋙ supported X' Z' :=
  modelMap squareIso ambientPullback ≫ inv (targetComparison f Z')

/-- The canonical pullback component on additive derived global sections with support. -/
@[stacks 0G79 "pullback on derived global sections with support"]
noncomputable abbrev app (K : DerivedCategory X.Modules) :
    (supported X Z).obj K ⟶
      (modulePullbackDerived f ⋙ supported X' Z').obj K :=
  (map squareIso ambientPullback).app K

/-- The supported pullback component is obtained by transporting the ambient-model component
across the target comparison. -/
@[stacks 0G79 "component of pullback on derived global sections with support", simp]
theorem map_app (K : DerivedCategory X.Modules) :
    (map squareIso ambientPullback).app K =
      modelApp squareIso ambientPullback K ≫
        inv ((targetComparison f Z').app K) := sorry

/-- An objectwise supported pullback component is compatible with the ambient model when it
satisfies the target-comparison equation. -/
@[stacks 0G79 "objectwise specification of supported pullback"]
abbrev IsMapAt (K : DerivedCategory X.Modules)
    (η : (supported X Z).obj K ⟶
      (modulePullbackDerived f ⋙ supported X' Z').obj K) : Prop :=
  η ≫ (targetComparison f Z').app K = modelApp squareIso ambientPullback K

/-- The canonical supported pullback component satisfies its target-comparison equation. -/
@[stacks 0G79 "objectwise specification of supported pullback"]
theorem app_isMapAt (K : DerivedCategory X.Modules) :
    IsMapAt squareIso ambientPullback K (app squareIso ambientPullback K) := sorry

/-- An objectwise supported pullback component satisfying the target-comparison equation is the
canonical component. -/
@[stacks 0G79 "uniqueness of supported pullback components"]
theorem IsMapAt.eq_app {K : DerivedCategory X.Modules}
    {η : (supported X Z).obj K ⟶
      (modulePullbackDerived f ⋙ supported X' Z').obj K}
    (hη : IsMapAt squareIso ambientPullback K η) :
    η = app squareIso ambientPullback K := sorry

/-- A supported pullback transformation is compatible with the ambient model when it satisfies
the target-comparison equation. -/
@[stacks 0G79 "specification of supported pullback"]
abbrev IsMap (η : supported X Z ⟶ modulePullbackDerived f ⋙ supported X' Z') : Prop :=
  η ≫ targetComparison f Z' = modelMap squareIso ambientPullback

/-- The canonical supported pullback transformation satisfies its target-comparison equation. -/
@[stacks 0G79 "specification of supported pullback"]
theorem map_isMap :
    IsMap squareIso ambientPullback (map squareIso ambientPullback) := sorry

/-- A supported pullback transformation satisfying the target-comparison equation is the
canonical transformation. -/
@[stacks 0G79 "uniqueness of supported pullback transformations"]
theorem IsMap.eq_map
    {η : supported X Z ⟶ modulePullbackDerived f ⋙ supported X' Z'}
    (hη : IsMap squareIso ambientPullback η) :
    η = map squareIso ambientPullback := sorry

/-- The supported pullback transformation is characterized by its ambient realization. -/
@[stacks 0G79 "pullback on derived global sections with support specification"]
theorem map_comp_targetComparison :
    map squareIso ambientPullback ≫ targetComparison f Z' =
      modelMap squareIso ambientPullback := sorry

/-- The canonical supported pullback component is characterized by its ambient realization. -/
@[stacks 0G79 "pullback on derived global sections with support specification"]
theorem app_comp_targetComparison (K : DerivedCategory X.Modules) :
    app squareIso ambientPullback K ≫
        (targetComparison f Z').app K =
      modelApp squareIso ambientPullback K := sorry

/-- Pullback on derived global sections with support commutes with forgetting support. -/
@[stacks 0G79 "derived supported pullback and forget-support compatibility"]
theorem map_comp_forget :
    map squareIso ambientPullback ≫
        Functor.whiskerLeft (modulePullbackDerived f) (forget X' Z') =
      forget X Z ≫ ambientPullback := sorry

/-- Pullback on derived global sections with support commutes with forgetting support. -/
@[stacks 0G79 "derived supported pullback and forget-support square"]
theorem forgetCommSq (K : DerivedCategory X.Modules) :
    CommSq
      (app squareIso ambientPullback K)
      ((forget X Z).app K)
      ((Functor.whiskerLeft (modulePullbackDerived f) (forget X' Z')).app K)
      (ambientPullback.app K) := sorry

/-- The degree-`n` cohomology map induced by supported pullback. -/
@[stacks 0G79 "pullback on cohomology with support"]
abbrev cohomologyApp (K : DerivedCategory X.Modules) (n : ℤ) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat n).map
    (app squareIso ambientPullback K)

/-- Pullback on cohomology with support commutes with the maps that forget support. -/
@[stacks 0G79 "cohomology supported pullback and forget-support square"]
theorem cohomologyCommSq (K : DerivedCategory X.Modules) (n : ℤ) :
    CommSq
      (cohomologyApp squareIso ambientPullback K n)
      ((DerivedCategory.homologyFunctor AddCommGrpCat n).map ((forget X Z).app K))
      ((DerivedCategory.homologyFunctor AddCommGrpCat n).map
        ((Functor.whiskerLeft (modulePullbackDerived f) (forget X' Z')).app K))
      ((DerivedCategory.homologyFunctor AddCommGrpCat n).map (ambientPullback.app K)) := sorry

end AlgebraicGeometry.RingedSpace.ClosedSubset.GlobalSectionsWithSupport.BaseChange
