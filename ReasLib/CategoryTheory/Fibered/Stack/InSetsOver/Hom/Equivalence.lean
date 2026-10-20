/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.Hom.Computations

/-!
# Hom equivalences for stacks in sets

This file packages the equivalence between stack morphisms and set-fibred morphisms and the
ambient induced-bicategory Hom equivalence.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Bicategory ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Sets.Hom

variable {J : GrothendieckTopology C}
variable {X Y : StackOver.Sets J}

/-- Equivalence over the base can be tested after forgetting a morphism of stacks in sets to
stacks in setoids. -/
@[stacks 042Z "set-stack Hom equivalence criterion"]
theorem isEquivalence_iff_toSetoidsMor (F : X ⟶ Y) :
    IsEquivalence F ↔
      StackOver.Setoids.Hom.IsEquivalence (toSetoidsMor F) := sorry

/-- Morphisms of stacks in sets are canonically equivalent to morphisms of their underlying
categories fibred in sets. -/
@[stacks 042Z "set-stack Hom carrier equivalence"]
def setsEquiv : (X.toSets ⟶ Y.toSets) ≃ (X ⟶ Y) where
  toFun := ofSetsMor
  invFun := toSetsMor
  left_inv := toSetsMor.ofSetsMor
  right_inv := ofSetsMor.toSetsMor

/-- Applying the canonical Hom equivalence lifts a set-fibred morphism. -/
@[simp, stacks 042Z "set-stack Hom carrier equivalence application"]
theorem setsEquiv.apply (F : X.toSets ⟶ Y.toSets) :
    setsEquiv F = ofSetsMor F := sorry

/-- Applying the inverse canonical Hom equivalence forgets a stack morphism to its set-fibred
representative. -/
@[simp, stacks 042Z "set-stack Hom carrier equivalence inverse application"]
theorem setsEquiv.symm_apply (F : X ⟶ Y) :
    setsEquiv.symm F = toSetsMor F := sorry

/-- The canonical equivalence from the ambient setoid-stack Hom category to the Hom category of
stacks in sets. -/
@[stacks 042Z "set-stack ambient Hom category equivalence"]
abbrev ambientEquivalence :
    (X.toSetoids ⟶ Y.toSetoids) ≌ (X ⟶ Y) :=
  Bicategory.InducedBicategory.homEquivalence X Y

/-- The forgetful functor from the Hom category of stacks in sets to the ambient Hom category of
stacks in setoids. -/
@[stacks 042Z "set-stack ambient Hom forgetful functor"]
abbrev ambientFunctor :
    (X ⟶ Y) ⥤ (X.toSetoids ⟶ Y.toSetoids) :=
  ambientEquivalence.inverse

/-- Lift an isomorphism of ambient stack-in-setoids morphisms to the induced Hom category of
stacks in sets. -/
@[stacks 042Z "set-stack ambient Hom isomorphism lift"]
noncomputable def isoMk {F G : X ⟶ Y}
    (e : toSetoidsMor F ≅ toSetoidsMor G) : F ≅ G :=
  Bicategory.InducedBicategory.isoMk e

end StackOver.Sets.Hom

end CategoryTheory
