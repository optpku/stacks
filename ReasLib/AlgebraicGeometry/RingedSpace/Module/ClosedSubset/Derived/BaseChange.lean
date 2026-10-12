/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.ClosedSubset.Derived
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.CategoryTheory.Adjunction.BaseChange
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived base change for modules supported on a closed subset

This file specializes the categorical mate construction to the derived adjunction between
closed-subset direct image and sections with support. The pullback functor on closed subsets and
its comparison with ambient pullback remain explicit geometric inputs.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ClosedSubset.DerivedBaseChange

variable {X X' : RingedSpace.{u}}
variable {f : X' ⟶ X} {Z : Closeds X} {Z' : Closeds X'}
variable {closedPullback : ModuleDerived X Z ⥤ ModuleDerived X' Z'}
variable (squareIso :
  closedPullback ⋙ Pushforward.derived X' Z' ≅
    Pushforward.derived X Z ⋙ modulePullbackDerived f)

/-- The source of closed-support derived base change. -/
@[stacks 0G78 "closed-support derived base-change source"]
abbrev source (Z : Closeds X) (Z' : Closeds X')
    (closedPullback : ModuleDerived X Z ⥤ ModuleDerived X' Z') :
    DerivedCategory X.Modules ⥤ ModuleDerived X' Z' :=
  SectionsWithSupport.derived X Z ⋙ closedPullback

/-- The target of closed-support derived base change. -/
@[stacks 0G78 "closed-support derived base-change target"]
abbrev target (f : X' ⟶ X) (Z' : Closeds X') :
    DerivedCategory X.Modules ⥤ ModuleDerived X' Z' :=
  modulePullbackDerived f ⋙ SectionsWithSupport.derived X' Z'

/-- The derived base-change transformation for sections with support. -/
@[stacks 0G78 "closed-support derived base-change map"]
noncomputable abbrev map :
    source Z Z' closedPullback ⟶ target f Z' :=
  CategoryTheory.DerivedBaseChange.map
    (Derived.adjunction X Z) (Derived.adjunction X' Z') squareIso

/-- The component of closed-support derived base change at an ambient derived module. -/
@[stacks 0G78 "closed-support derived base-change component"]
noncomputable abbrev app (K : DerivedCategory X.Modules) :
    (source Z Z' closedPullback).obj K ⟶ (target f Z').obj K :=
  (map squareIso).app K

/-- The objectwise mate specification for a closed-support base-change component. -/
@[stacks 0G78 "closed-support derived base-change component specification"]
abbrev IsMapAt (K : DerivedCategory X.Modules)
    (η : (source Z Z' closedPullback).obj K ⟶ (target f Z').obj K) : Prop :=
  CategoryTheory.DerivedBaseChange.IsMapAt
    (Derived.adjunction X Z) (Derived.adjunction X' Z') squareIso K η

/-- The canonical closed-support base-change component satisfies its mate equation. -/
@[stacks 0G78 "closed-support derived base-change component specification"]
theorem app_isMapAt (K : DerivedCategory X.Modules) :
    IsMapAt squareIso K (app squareIso K) := sorry

/-- A transformation is the closed-support base-change map when it satisfies the canonical mate
equation. -/
@[stacks 0G78 "closed-support derived base-change specification"]
abbrev IsMap (η : source Z Z' closedPullback ⟶ target f Z') : Prop :=
  CategoryTheory.DerivedBaseChange.IsMap
    (Derived.adjunction X Z) (Derived.adjunction X' Z') squareIso η

/-- The canonical closed-support base-change transformation satisfies its mate equation. -/
@[stacks 0G78 "closed-support derived base-change specification"]
theorem map_isMap :
    IsMap squareIso (map squareIso) := sorry

/-- Transposing a closed-support base-change component recovers the pushforward comparison
followed by ambient pullback of the counit. -/
@[stacks 0G78 "closed-support derived base-change component specification"]
theorem app_spec (K : DerivedCategory X.Modules) :
    (((Derived.adjunction X' Z').homEquiv
        (closedPullback.obj ((SectionsWithSupport.derived X Z).obj K))
        ((modulePullbackDerived f).obj K)).symm
        (app squareIso K)) =
      squareIso.hom.app ((SectionsWithSupport.derived X Z).obj K) ≫
        (modulePullbackDerived f).map
          ((Derived.adjunction X Z).counit.app K) := sorry

/-- A component satisfying the closed-support mate equation is the canonical component. -/
@[stacks 0G78 "uniqueness of closed-support derived base-change components"]
theorem IsMapAt.eq_app {K : DerivedCategory X.Modules}
    {η : (source Z Z' closedPullback).obj K ⟶ (target f Z').obj K}
    (hη : IsMapAt squareIso K η) :
    η = app squareIso K := sorry

/-- A transformation satisfying the closed-support mate equation is the canonical map. -/
@[stacks 0G78 "uniqueness of closed-support derived base-change maps"]
theorem IsMap.eq_map
    {η : source Z Z' closedPullback ⟶ target f Z'}
    (hη : IsMap squareIso η) :
    η = map squareIso := sorry

/-- Closed-support base change commutes with the counits of the two derived adjunctions. -/
@[stacks 0G78 "closed-support derived base-change counit square"]
theorem counitCommSq (K : DerivedCategory X.Modules) :
    CommSq
      (squareIso.inv.app ((SectionsWithSupport.derived X Z).obj K) ≫
        (Pushforward.derived X' Z').map (app squareIso K))
      ((modulePullbackDerived f).map
        ((Derived.adjunction X Z).counit.app K))
      ((Derived.adjunction X' Z').counit.app
        ((modulePullbackDerived f).obj K))
      (𝟙 ((modulePullbackDerived f).obj K)) := sorry

/-- The componentwise counit equation for closed-support derived base change. -/
@[stacks 0G78 "closed-support derived base-change counit compatibility"]
theorem app_comp_counit (K : DerivedCategory X.Modules) :
    squareIso.inv.app ((SectionsWithSupport.derived X Z).obj K) ≫
        (Pushforward.derived X' Z').map (app squareIso K) ≫
          (Derived.adjunction X' Z').counit.app
            ((modulePullbackDerived f).obj K) =
      (modulePullbackDerived f).map
        ((Derived.adjunction X Z).counit.app K) := sorry

end AlgebraicGeometry.RingedSpace.ClosedSubset.DerivedBaseChange
