/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.Over.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of bundled stacks

This file exposes the ambient, based, total-category, and fiberwise views of a morphism of
bundled stacks, together with constructors and round-trip computation lemmas.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

namespace StackOver.Hom

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {X Y Z : StackOver.{u, v, w, vS} J}

/-- The underlying morphism of fibered categories. -/
@[stacks 02ZG "underlying morphism of bundled stacks"]
abbrev toMor (F : X ⟶ Y) : X.toFiberedCategoryOver ⟶ Y.toFiberedCategoryOver := F.hom

/-- Forget a `2`-isomorphism of stack morphisms to the corresponding ambient
`2`-isomorphism of fibred-category morphisms. -/
@[stacks 02ZG "ambient 2-isomorphism of bundled stacks"]
def toMorIso {F G : X ⟶ Y} (e : F ≅ G) : toMor F ≅ toMor G :=
  Bicategory.InducedBicategory.Iso.toAmbient e

namespace toMorIso

/-- The ambient forward `2`-cell of `toMorIso e` is the forward cell of `e`. -/
@[stacks 02ZG "forward ambient cell of a stack 2-isomorphism", simp]
theorem hom {F G : X ⟶ Y} (e : F ≅ G) :
    (toMorIso e).hom = e.hom.hom := sorry

/-- The ambient inverse `2`-cell of `toMorIso e` is the inverse cell of `e`. -/
@[stacks 02ZG "inverse ambient cell of a stack 2-isomorphism", simp]
theorem inv {F G : X ⟶ Y} (e : F ≅ G) :
    (toMorIso e).inv = e.inv.hom := sorry

end toMorIso

/-- The underlying based functor. -/
@[stacks 02ZG "based functor underlying a stack morphism"]
abbrev toBasedFunctor (F : X ⟶ Y) :=
  FiberedCategoryOver.toBasedFunctor (toMor F)

/-- The underlying functor on total categories. -/
@[stacks 02ZG "total functor underlying a stack morphism"]
abbrev toFunctor (F : X ⟶ Y) := (toBasedFunctor F).toFunctor

/-- The commutation: `toFunctor F ⋙ Y.p = X.p`. -/
@[stacks 02ZG "projection commutation of a stack morphism"]
abbrev comm (F : X ⟶ Y) : toFunctor F ⋙ Y.p = X.p := (toBasedFunctor F).w

/-- The induced functor on the fiber over `U`. -/
@[stacks 02ZG "fiber functor of a stack morphism"]
abbrev fiberFunctor (F : X ⟶ Y) (U : C) := (toBasedFunctor F).fiberFunctor U

/-- A morphism of bundled stacks is an equivalence over the base when its underlying based
functor is an equivalence. -/
@[stacks 046N "equivalence predicate for a stack morphism"]
abbrev IsEquivalence (F : X ⟶ Y) : Prop :=
  BasedFunctor.IsEquivalence (FiberedCategoryOver.toBasedFunctor (toMor F))

/-- Lift a morphism of fibered categories to a morphism of stacks. -/
@[stacks 02ZG "lift an ambient morphism to stacks"]
abbrev lift (F : X.toFiberedCategoryOver ⟶ Y.toFiberedCategoryOver) : X ⟶ Y :=
  Bicategory.InducedBicategory.mkHom F

/-- Build a morphism of stacks from a based functor that preserves strongly cartesian
morphisms. This is the stack-level constructor corresponding to
`FiberedCategoryOver.ofBasedFunctor`. -/
@[stacks 02ZG "construct a stack morphism from a based functor"]
def ofBasedFunctor
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (hF : F.PreservesStronglyCartesian) : X ⟶ Y :=
  lift (FiberedCategoryOver.ofBasedFunctor F hF)

namespace ofBasedFunctor

/-- The based functor underlying `ofBasedFunctor F hF` is `F`. -/
@[stacks 02ZG "based-functor constructor round trip", simp]
theorem toBasedFunctor
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (hF : F.PreservesStronglyCartesian) :
    StackOver.Hom.toBasedFunctor (ofBasedFunctor F hF) = F := sorry

/-- The total-category functor underlying `ofBasedFunctor F hF` is the total functor of `F`. -/
@[stacks 02ZG "total-functor constructor round trip", simp]
theorem toFunctor
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory)
    (hF : F.PreservesStronglyCartesian) :
    StackOver.Hom.toFunctor (ofBasedFunctor F hF) = F.toFunctor := sorry

end ofBasedFunctor

/-- Round-trip: lifting the underlying morphism recovers the original. -/
@[stacks 02ZG "ambient morphism lift round trip", simp]
theorem lift.toMor (F : X ⟶ Y) : lift (toMor F) = F := sorry

/-- Round-trip: extracting the underlying morphism of a lift. -/
@[stacks 02ZG "ambient morphism extraction round trip", simp]
theorem toMor.lift (F : X.toFiberedCategoryOver ⟶ Y.toFiberedCategoryOver) :
    toMor (lift F) = F := sorry

end StackOver.Hom

end CategoryTheory
