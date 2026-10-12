/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of stacks in setoids

This file provides the direct forgetful and lifting constructions between morphisms of stacks in
setoids and morphisms of the corresponding setoid-fibred categories.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Setoids.Hom

variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Setoids J}

/-- The underlying morphism in the ambient bicategory of stacks in groupoids. -/
@[stacks 0433 "stack-in-setoids groupoid morphism owner"]
abbrev toGroupoidsMor (F : X ⟶ Y) :
    X.toGroupoids ⟶ Y.toGroupoids :=
  (StackOver.Setoids.forget J).map F

/-- Forget a `2`-isomorphism of setoid-stack morphisms to the corresponding
`2`-isomorphism of groupoid-stack morphisms. -/
@[stacks 0433 "stack-in-setoids groupoid morphism isomorphism"]
def toGroupoidsMorIso {F G : X ⟶ Y} (e : F ≅ G) :
    toGroupoidsMor F ≅ toGroupoidsMor G :=
  Bicategory.InducedBicategory.Iso.toAmbient e

/-- The underlying morphism of categories fibred in setoids. -/
@[stacks 0433 "stack-in-setoids setoid morphism owner"]
def toSetoidsMor (F : X ⟶ Y) : X.toSetoids ⟶ Y.toSetoids :=
  FiberedCategoryOver.Setoids.ofBasedFunctor
    (StackOver.Groupoids.Hom.toBasedFunctor (toGroupoidsMor F))

/-- The explicit comparison from the composite of two underlying setoid-fibred morphisms to
the underlying setoid-fibred morphism of the composite stack morphism. -/
@[stacks 0433 "stack-in-setoids morphism composition comparison"]
def toSetoidsMor.compIso {Z : StackOver.Setoids J} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toSetoidsMor F ≫ toSetoidsMor G ≅ toSetoidsMor (F ≫ G) :=
  Bicategory.InducedBicategory.isoMk (Iso.refl _)

/-- Forget a `2`-isomorphism of setoid-stack morphisms to the corresponding
`2`-isomorphism of setoid-fibred morphisms. -/
@[stacks 0433 "stack-in-setoids morphism isomorphism owner"]
noncomputable def toSetoidsMorIso {F G : X ⟶ Y} (e : F ≅ G) :
    toSetoidsMor F ≅ toSetoidsMor G :=
  Bicategory.InducedBicategory.isoMk
    (FiberedCategoryOver.Groupoids.toBasedFunctorIso
        (Bicategory.InducedBicategory.Iso.toAmbient
          (Bicategory.InducedBicategory.Iso.toAmbient e)))

/-- The underlying morphism in the ambient bicategory of fibered categories. -/
@[stacks 0433 "stack-in-setoids fibered morphism owner"]
abbrev toFiberedMor (F : X ⟶ Y) :
    X.toFiberedCategoryOver ⟶ Y.toFiberedCategoryOver :=
  StackOver.Groupoids.Hom.toFiberedMor (toGroupoidsMor F)

/-- The underlying based functor of a morphism of stacks in setoids. -/
@[stacks 0433 "stack-in-setoids based functor owner"]
abbrev toBasedFunctor (F : X ⟶ Y) :=
  FiberedCategoryOver.Setoids.toBasedFunctor (toSetoidsMor F)

/-- Forget a `2`-isomorphism of setoid-stack morphisms directly to the corresponding
isomorphism of based functors. -/
@[stacks 0433 "stack-in-setoids based morphism isomorphism"]
noncomputable def toBasedFunctorIso {F G : X ⟶ Y} (e : F ≅ G) :
    toBasedFunctor F ≅ toBasedFunctor G :=
  FiberedCategoryOver.Setoids.toBasedFunctorIso (toSetoidsMorIso e)

/-- The underlying total-category functor of a morphism of stacks in setoids. -/
@[stacks 0433 "stack-in-setoids total morphism owner"]
abbrev toFunctor (F : X ⟶ Y) :=
  FiberedCategoryOver.Setoids.toFunctor (toSetoidsMor F)

/-- The strict commutation of the underlying total functor with the projections. -/
@[stacks 0433 "stack-in-setoids morphism projection equation"]
abbrev comm (F : X ⟶ Y) : toFunctor F ⋙ Y.p = X.p :=
  FiberedCategoryOver.Setoids.comm (toSetoidsMor F)

/-- The induced functor on the fiber over `U`. -/
@[stacks 0433 "stack-in-setoids fiber morphism owner"]
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  FiberedCategoryOver.Setoids.fiberFunctor (toSetoidsMor F) U

/-- A morphism of stacks in setoids is an equivalence over the base when its underlying based
functor is an equivalence. -/
@[stacks 0433 "stack-in-setoids morphism equivalence predicate"]
abbrev IsEquivalence (F : X ⟶ Y) : Prop := (toBasedFunctor F).IsEquivalence

namespace toSetoidsMor

/-- The based-functor view of `toSetoidsMor F` is the canonical groupoid-stack based-functor
view of `F`. -/
@[simp, stacks 0433 "stack-in-setoids based morphism readout"]
theorem toBasedFunctor (F : X ⟶ Y) :
    FiberedCategoryOver.Setoids.toBasedFunctor (toSetoidsMor F) =
      StackOver.Groupoids.Hom.toBasedFunctor (toGroupoidsMor F) := sorry

end toSetoidsMor

/-- Lift an ambient stack-in-groupoids morphism to a morphism of stacks in setoids. -/
@[stacks 0433 "stack-in-setoids groupoid morphism lift"]
abbrev lift (F : X.toGroupoids ⟶ Y.toGroupoids) : X ⟶ Y :=
  Bicategory.InducedBicategory.mkHom F

/-- Lift a morphism of the underlying categories fibred in setoids to a morphism of stacks in
setoids. This is the inverse owner bridge to `toSetoidsMor`. -/
@[stacks 0433 "stack-in-setoids setoid morphism lift"]
def ofSetoidsMor (F : X.toSetoids ⟶ Y.toSetoids) : X ⟶ Y :=
  lift (StackOver.Groupoids.Hom.lift
    (FiberedCategoryOver.Groupoids.ofBasedFunctor
      (FiberedCategoryOver.Setoids.toBasedFunctor F)))

end StackOver.Setoids.Hom

end CategoryTheory
