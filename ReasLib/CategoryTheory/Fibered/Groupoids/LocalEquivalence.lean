/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryOver.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification.LocalEquivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Local equivalences of categories fibred in groupoids

The groupoid-fibred bicategory has the same site-local notion of equivalence as the ambient
fibered-category bicategory.  This leaf owns the forgetful abbreviation, so applications do not
repeat the `toFibered` map at every occurrence.
-/

@[expose] public section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Groupoids.Hom

variable {X Y : FiberedCategoryOver.Groupoids C}

/- The abbreviation is intentionally transparent: all closure theorems remain inherited from the
ambient `FiberedCategoryOver.Hom` owner. -/

/-- A groupoid-fibred morphism is a local equivalence when its ambient fibered-category map is. -/
@[stacks 02ZP "groupoid-fibred local equivalence"]
abbrev IsLocalEquivalence (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  FiberedCategoryOver.Hom.IsLocalEquivalence J
    ((FiberedCategoryOver.Groupoids.toFibered C).map F)

/-- A groupoid-fibred morphism is a stackification when its ambient map is. -/
@[stacks 02ZP "groupoid-fibred stackification predicate"]
abbrev IsStackification (J : GrothendieckTopology C) (F : X ⟶ Y) : Prop :=
  FiberedCategoryOver.Hom.IsStackification J
    ((FiberedCategoryOver.Groupoids.toFibered C).map F)

namespace IsStackification

/-- A stackification of groupoid-fibred categories is a local equivalence. -/
theorem isLocalEquivalence
    {J : GrothendieckTopology C} {F : X ⟶ Y}
    (hF : IsStackification J F) :
    IsLocalEquivalence J F := sorry

end IsStackification

end FiberedCategoryOver.Groupoids.Hom

end CategoryTheory
