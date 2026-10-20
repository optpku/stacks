module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pullback
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pullback of perfect derived modules on ringed spaces

This file specializes preservation of perfectness to the canonical derived pullback of module
sheaves on ringed spaces.  All construction and instance data are supplied by the reusable
ringed-space pullback API.
-/

open AlgebraicGeometry
open CategoryTheory
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X Y : RingedSpace.{u}}

/-- If `E` is perfect in `D(𝒪_Y)`, then its derived pullback along `f : X ⟶ Y` is
perfect in `D(𝒪_X)`. -/
@[stacks 09UA]
theorem modulePullbackDerived_isPerfect
    (f : X ⟶ Y) (E : ModuleDerived Y) (hE : ModuleDerived.IsPerfect E) :
    ModuleDerived.IsPerfect ((L(f)^*).obj E) := sorry

/-- Derived pullback restricted to the full subcategories of perfect derived `𝒪`-modules. -/
@[stacks 09UA "perfect pullback functor"]
noncomputable def modulePullbackPerfect (f : X ⟶ Y) :
    ModuleDerived.Perfect (X := Y) ⥤ ModuleDerived.Perfect (X := X) :=
  ObjectProperty.FullSubcategory.restrict
    (P := ModuleDerived.perfect (X := Y))
    (Q := ModuleDerived.perfect (X := X))
    (L(f)^*)
    (modulePullbackDerived_isPerfect f)

/-- After forgetting perfectness, `modulePullbackPerfect` is the ordinary derived pullback. -/
@[stacks 09UA "perfect pullback inclusion comparison"]
noncomputable def modulePullbackPerfectCompιIso (f : X ⟶ Y) :
    modulePullbackPerfect f ⋙ ModuleDerived.Perfect.ι (X := X) ≅
      ModuleDerived.Perfect.ι (X := Y) ⋙ (L(f)^*) :=
  ObjectProperty.FullSubcategory.restrict.compιIso
    (P := ModuleDerived.perfect (X := Y))
    (Q := ModuleDerived.perfect (X := X))
    (L(f)^*)
    (modulePullbackDerived_isPerfect f)

end AlgebraicGeometry.RingedSpace
