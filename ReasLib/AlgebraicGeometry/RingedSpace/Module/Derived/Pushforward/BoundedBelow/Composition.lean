/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward.BoundedBelow
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Pushforward.BoundedBelow.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of bounded-below derived pushforwards on ringed spaces

The generic bounded-below right-derived composition API is specialized here using the canonical
underived composition isomorphism for direct images of module sheaves.
-/

@[expose] public section

open AlgebraicGeometry.RingedSpace.Hom

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.moduleDerivedPushforwardPlus

variable {X Y Z : RingedSpace.{u}}

/-- The canonical comparison from bounded-below derived pushforward along a composite to the
composite of the two bounded-below derived pushforwards. -/
@[stacks 01F5 "bounded-below derived pushforward composition comparison"]
noncomputable def compComparison (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleDerivedPushforwardPlus (f ≫ g) ⟶
      moduleDerivedPushforwardPlus f ⋙ moduleDerivedPushforwardPlus g :=
  Functor.RightDerived.Composition.BoundedBelow.comparisonOfIso
    (pushforward f) (pushforward g) (RingedSpace.Hom.pushforwardCompIso f g)

/-- Lemma 20.13.7: the canonical bounded-below derived pushforward comparison for composable
morphisms of ringed spaces is an isomorphism. -/
@[stacks 01F5]
noncomputable instance compComparison_isIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    IsIso (compComparison f g) := sorry

/-- Bounded-below derived pushforward on ringed spaces is pseudofunctorial under composition. -/
@[stacks 01F5 "bounded-below derived pushforward composition isomorphism"]
noncomputable def compIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    moduleDerivedPushforwardPlus (f ≫ g) ≅
      moduleDerivedPushforwardPlus f ⋙ moduleDerivedPushforwardPlus g :=
  asIso (compComparison f g)

/-- The forward map of `compIso` is the canonical bounded-below composition comparison. -/
@[simp, stacks 01F5 "bounded-below derived pushforward composition map"]
theorem compIso_hom (f : X ⟶ Y) (g : Y ⟶ Z) :
    (compIso f g).hom = compComparison f g := sorry

end AlgebraicGeometry.RingedSpace.moduleDerivedPushforwardPlus
