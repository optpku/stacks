/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetoidsOver.Hom.Computations

/-!
# Hom equivalences for stacks in setoids

This file packages the equivalence between stack morphisms and setoid-fibred morphisms and the
ambient induced-bicategory Hom equivalence.
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

/-- Morphisms of stacks in setoids are canonically equivalent to morphisms of their underlying
categories fibred in setoids. -/
@[stacks 0433 "setoid-stack Hom carrier equivalence"]
def setoidsEquiv : (X.toSetoids ⟶ Y.toSetoids) ≃ (X ⟶ Y) where
  toFun := ofSetoidsMor
  invFun := toSetoidsMor
  left_inv := toSetoidsMor.ofSetoidsMor
  right_inv := ofSetoidsMor.toSetoidsMor

/-- Applying the canonical Hom equivalence lifts a setoid-fibred morphism. -/
@[simp, stacks 0433 "setoid-stack Hom carrier equivalence application"]
theorem setoidsEquiv.apply (F : X.toSetoids ⟶ Y.toSetoids) :
    setoidsEquiv F = ofSetoidsMor F := sorry

/-- Applying the inverse canonical Hom equivalence forgets a stack morphism to its
setoid-fibred representative. -/
@[simp, stacks 0433 "setoid-stack Hom carrier equivalence inverse application"]
theorem setoidsEquiv.symm_apply (F : X ⟶ Y) :
    setoidsEquiv.symm F = toSetoidsMor F := sorry

/-- Equivalence of a morphism of stacks in setoids can be tested after forgetting only to the
stack-in-groupoids owner. -/
@[stacks 0433 "setoid-stack Hom equivalence criterion"]
theorem isEquivalence_iff_toGroupoidsMor (F : X ⟶ Y) :
    IsEquivalence F ↔
      StackOver.Groupoids.Hom.IsEquivalence (toGroupoidsMor F) := sorry

/-- The canonical equivalence from the ambient groupoid-stack Hom category to the Hom category
of stacks in setoids. -/
@[stacks 0433 "setoid-stack ambient Hom category equivalence"]
abbrev ambientEquivalence :
    (X.toGroupoids ⟶ Y.toGroupoids) ≌ (X ⟶ Y) :=
  Bicategory.InducedBicategory.homEquivalence X Y

/-- The forgetful functor between the induced hom-categories. -/
@[stacks 0433 "setoid-stack ambient Hom forgetful functor"]
abbrev ambientFunctor :
    (X ⟶ Y) ⥤ (X.toGroupoids ⟶ Y.toGroupoids) :=
  ambientEquivalence.inverse

/-- Lift an isomorphism of ambient stack-in-groupoids morphisms to the induced hom-category. -/
@[stacks 0433 "setoid-stack ambient Hom isomorphism lift"]
noncomputable def isoMk {F G : X ⟶ Y}
    (e : toGroupoidsMor F ≅ toGroupoidsMor G) : F ≅ G :=
  Bicategory.InducedBicategory.isoMk e

end StackOver.Setoids.Hom

end CategoryTheory
