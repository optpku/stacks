/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bundled categorical universe lifts

Canonical `Cat` owners for lifting only the object universe, or the object and morphism universes
independently. Bundling the category structure avoids repeating local registrations of mathlib's
intentionally non-global `uliftCategory` instance.
-/

@[expose] public section

universe u v w v'

namespace CategoryTheory

namespace Cat

/-- The object-universe lift of `C`, bundled with mathlib's canonical `uliftCategory` structure.

The structure is stored in the `Cat` value rather than registered globally, since a global
`Category (ULift C)` instance has a known diamond for preordered categories. -/
@[stacks 02XS "bundled object-universe resizing for fibred-category owners"]
def objULift (C : Type u) [Category.{v} C] : Cat.{v, max w u} :=
  @Cat.of (ULift.{w} C) (@uliftCategory C _)

namespace ObjULift

/-- The canonical equivalence with the bundled object-universe lift. -/
abbrev equiv (C : Type u) [Category.{v} C] :
    C ≌ objULift.{u, v, w} C :=
  ULift.equivalence

/-- The canonical functor from a category to its bundled object-universe lift. -/
abbrev up (C : Type u) [Category.{v} C] :
    C ⥤ objULift.{u, v, w} C :=
  (equiv.{u, v, w} C).functor

/-- The canonical functor forgetting a bundled object-universe lift. -/
abbrev down (C : Type u) [Category.{v} C] :
    objULift.{u, v, w} C ⥤ C :=
  (equiv.{u, v, w} C).inverse

end ObjULift

/-- The independent object- and morphism-universe lift of `C`, bundled with its canonical category
structure. Its carrier is `ULiftHom (ULift C)`. -/
@[stacks 0046 "bundled two-universe resizing for representable fibred groupoids"]
def twoULift (C : Type u) [Category.{v} C] : Cat.{max v' v, max w u} :=
  @Cat.of (ULiftHom.{v'} (ULift.{w} C))
    (@ULiftHom.category (ULift.{w} C) (@uliftCategory C _))

namespace TwoULift

/-- The canonical equivalence with the bundled two-universe lift. -/
abbrev equiv (C : Type u) [Category.{v} C] :
    C ≌ twoULift.{u, v, w, v'} C :=
  ULiftHomULiftCategory.equiv C

/-- The canonical functor from a category to its bundled two-universe lift. -/
abbrev up (C : Type u) [Category.{v} C] :
    C ⥤ twoULift.{u, v, w, v'} C :=
  (equiv.{u, v, w, v'} C).functor

/-- The canonical functor forgetting a bundled two-universe lift. -/
abbrev down (C : Type u) [Category.{v} C] :
    twoULift.{u, v, w, v'} C ⥤ C :=
  (equiv.{u, v, w, v'} C).inverse

end TwoULift

end Cat

end CategoryTheory
