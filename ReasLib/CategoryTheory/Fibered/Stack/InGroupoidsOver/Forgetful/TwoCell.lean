/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Forgetful.Action
import Mathlib.Tactic.CrossRefAttribute

/-!
# Two-cell action of the groupoid-stack forgetful pseudofunctor

This file names the groupoid-fibred, based, total-category, and fiber projections of stack
`2`-cells and records their identity, composition, and pseudofunctor readouts.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace StackOver.Groupoids

variable {J : GrothendieckTopology C}

namespace Hom₂

variable {X Y : StackOver.Groupoids.{u, v, w, vS} J}
variable {F G : X ⟶ Y}

/-- Forget a stack `2`-morphism to its groupoid-fibred natural transformation. -/
@[stacks 02ZK "underlying groupoid-fibred natural transformation of a stack 2-morphism"]
def toGroupoidsNatTrans (eta : F ⟶ G) :
    (StackOver.Groupoids.forget J).map F ⟶
      (StackOver.Groupoids.forget J).map G :=
  eta.hom

/-- The based natural transformation underlying a stack `2`-morphism. -/
@[stacks 02ZK "underlying based natural transformation of a stack 2-morphism"]
def toBasedNatTrans (eta : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toBasedFunctor
          ((StackOver.Groupoids.forget J).map F) ⟶
      FiberedCategoryOver.Groupoids.toBasedFunctor
        ((StackOver.Groupoids.forget J).map G) :=
  (toGroupoidsNatTrans eta).hom

/-- The natural transformation on total categories underlying a stack `2`-morphism. -/
@[stacks 02ZK "underlying total natural transformation of a stack 2-morphism"]
def toNatTrans (eta : F ⟶ G) :
    FiberedCategoryOver.Groupoids.toFunctor
          ((StackOver.Groupoids.forget J).map F) ⟶
      FiberedCategoryOver.Groupoids.toFunctor
        ((StackOver.Groupoids.forget J).map G) :=
  (toBasedNatTrans eta).toNatTrans

/-- The groupoid-fibred projection sends an identity `2`-morphism to an identity. -/
@[simp, stacks 02ZK "groupoid-fibred identity readout of a stack 2-morphism"]
theorem toGroupoidsNatTrans.id (F : X ⟶ Y) :
    toGroupoidsNatTrans (𝟙 F) =
      𝟙 ((StackOver.Groupoids.forget J).map F) := rfl

/-- The groupoid-fibred projection preserves vertical composition. -/
@[simp, stacks 02ZK "groupoid-fibred composition readout of a stack 2-morphism"]
theorem toGroupoidsNatTrans.comp {H : X ⟶ Y}
    (eta : F ⟶ G) (theta : G ⟶ H) :
    toGroupoidsNatTrans (eta ≫ theta) =
      toGroupoidsNatTrans eta ≫ toGroupoidsNatTrans theta := rfl

/-- The based projection sends an identity `2`-morphism to an identity. -/
@[simp, stacks 02ZK "based identity readout of a stack 2-morphism"]
theorem toBasedNatTrans.id (F : X ⟶ Y) :
    toBasedNatTrans (𝟙 F) =
      𝟙 (FiberedCategoryOver.Groupoids.toBasedFunctor
        ((StackOver.Groupoids.forget J).map F)) := rfl

/-- The based projection preserves vertical composition. -/
@[simp, stacks 02ZK "based composition readout of a stack 2-morphism"]
theorem toBasedNatTrans.comp {H : X ⟶ Y}
    (eta : F ⟶ G) (theta : G ⟶ H) :
    toBasedNatTrans (eta ≫ theta) =
      toBasedNatTrans eta ≫ toBasedNatTrans theta := rfl

/-- The total-category projection sends an identity `2`-morphism to an identity. -/
@[simp, stacks 02ZK "total identity readout of a stack 2-morphism"]
theorem toNatTrans.id (F : X ⟶ Y) :
    toNatTrans (𝟙 F) =
      𝟙 (FiberedCategoryOver.Groupoids.toFunctor
        ((StackOver.Groupoids.forget J).map F)) := rfl

/-- The total-category projection preserves vertical composition. -/
@[simp, stacks 02ZK "total composition readout of a stack 2-morphism"]
theorem toNatTrans.comp {H : X ⟶ Y}
    (eta : F ⟶ G) (theta : G ⟶ H) :
    toNatTrans (eta ≫ theta) =
      NatTrans.vcomp (toNatTrans eta) (toNatTrans theta) := rfl

end Hom₂

namespace forget

/-- The `2`-cell action of the forgetful pseudofunctor is the named groupoid-fibred
projection. -/
@[simp, stacks 02ZK "groupoid-stack forgetful two-cell"]
theorem map₂.toGroupoidsNatTrans
    {X Y : StackOver.Groupoids.{u, v, w, vS} J}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    (StackOver.Groupoids.forget J).map₂ eta =
      Hom₂.toGroupoidsNatTrans eta := rfl

/-- The based natural transformation underlying a mapped `2`-cell is the named based
projection. -/
@[simp, stacks 02ZK "groupoid-stack forgetful two-cell based projection"]
theorem map₂.toBasedNatTrans
    {X Y : StackOver.Groupoids.{u, v, w, vS} J}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    ((StackOver.Groupoids.forget J).map₂ eta).hom =
      Hom₂.toBasedNatTrans eta := rfl

/-- The total natural transformation underlying a mapped `2`-cell is the named total-category
projection. -/
@[simp, stacks 02ZK "groupoid-stack forgetful two-cell total projection"]
theorem map₂.toNatTrans
    {X Y : StackOver.Groupoids.{u, v, w, vS} J}
    {F G : X ⟶ Y} (eta : F ⟶ G) :
    ((StackOver.Groupoids.forget J).map₂ eta).hom.toNatTrans =
      Hom₂.toNatTrans eta := rfl

/-- Restricting a mapped `2`-cell to a fiber agrees with restricting its named based
projection. -/
@[simp, stacks 02ZK "groupoid-stack forgetful two-cell fiber restriction"]
theorem map₂.fiber
    {X Y : StackOver.Groupoids.{u, v, w, vS} J}
    {F G : X ⟶ Y} (eta : F ⟶ G) (U : C) :
    BasedNatTrans.fiber ((StackOver.Groupoids.forget J).map₂ eta).hom U =
      BasedNatTrans.fiber (Hom₂.toBasedNatTrans eta) U := rfl

end forget

end StackOver.Groupoids

end CategoryTheory
