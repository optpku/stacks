/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Shift.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Represented Hom towers for sequential diagrams

@stack 0CQX

This leaf owns the inverse systems `n ↦ Hom_D(K_n, L)` and
`n ↦ Hom_D(K_n, L[-1])`, together with their transition and target-functoriality API.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u v

namespace CategoryTheory.HomotopyColimit.RepresentedHom

variable {D : Type u} [Category.{v} D] [Preadditive D]

/-- The inverse system `n ↦ Hom_D(K_n, L)` attached to a sequential diagram. -/
@[stacks 0CQX]
abbrev tower (K : ℕ ⥤ D) (L : D) : SequentialInverseSystem AddCommGrpCat :=
  K.op ⋙ preadditiveYoneda.obj L

/-- The `n`th object of the represented Hom tower is the group of maps `K_n ⟶ L`. -/
@[simp]
theorem tower_obj (K : ℕ ⥤ D) (L : D) (n : ℕ) :
    (tower K L).obj (op n) = AddCommGrpCat.of (K.obj n ⟶ L) := sorry

/-- A transition in the represented Hom tower acts by precomposition with the corresponding
map of the sequential diagram. -/
@[simp]
theorem tower_transitionMap_apply (K : ℕ ⥤ D) (L : D) {i j : ℕ}
    (hij : i ≤ j) (f : K.obj j ⟶ L) :
    (tower K L).transitionMap hij f = K.map (homOfLE hij) ≫ f := sorry

/-- Postcomposition with `f : L ⟶ M` gives a morphism of represented Hom towers. -/
@[stacks 0CQX]
def towerMap (K : ℕ ⥤ D) {L M : D} (f : L ⟶ M) :
    tower K L ⟶ tower K M :=
  Functor.whiskerLeft K.op (preadditiveYoneda.map f)

/-- The component of `towerMap` is the represented Hom map induced by its target morphism. -/
@[simp]
theorem towerMap_app (K : ℕ ⥤ D) {L M : D} (f : L ⟶ M) (n : ℕ) :
    (towerMap K f).app (op n) = (preadditiveYoneda.map f).app (op (K.obj n)) := sorry

/-- On elements, `towerMap` acts by postcomposition. -/
@[simp]
theorem towerMap_app_apply (K : ℕ ⥤ D) {L M : D} (f : L ⟶ M) (n : ℕ)
    (g : K.obj n ⟶ L) :
    (towerMap K f).app (op n) g = g ≫ f := sorry

/-- Postcomposition by an identity morphism induces the identity morphism of represented
Hom towers. -/
@[simp, stacks 0CQX]
theorem towerMap_id (K : ℕ ⥤ D) (L : D) :
    towerMap K (𝟙 L) = 𝟙 (tower K L) := sorry

/-- Postcomposition of target morphisms agrees with composition of the induced represented
Hom tower morphisms. -/
@[simp, stacks 0CQX]
theorem towerMap_comp (K : ℕ ⥤ D) {L M N : D} (f : L ⟶ M) (g : M ⟶ N) :
    towerMap K (f ≫ g) = towerMap K f ≫ towerMap K g := sorry

variable (K : ℕ ⥤ D) in
/-- The represented Hom tower as a functor of its target. -/
@[stacks 0CQX]
def towerFunctor : D ⥤ SequentialInverseSystem AddCommGrpCat where
  obj := tower K
  map := towerMap K
  map_id := towerMap_id K
  map_comp := towerMap_comp K

/-- The target functor for represented Hom towers evaluates to `tower K L`. -/
@[simp]
theorem towerFunctor_obj (K : ℕ ⥤ D) (L : D) :
    (towerFunctor K).obj L = tower K L := sorry

/-- The target functor for represented Hom towers sends a morphism to `towerMap`. -/
@[simp]
theorem towerFunctor_map (K : ℕ ⥤ D) {L M : D} (f : L ⟶ M) :
    (towerFunctor K).map f = towerMap K f := sorry

section Shift

variable [HasShift D ℤ]

/-- The shifted inverse system `n ↦ Hom_D(K_n, L[-1])` controlling the first derived-limit
term of the represented Hom sequence. -/
@[stacks 0CQX]
abbrev shiftedTower (K : ℕ ⥤ D) (L : D) : SequentialInverseSystem AddCommGrpCat :=
  tower K (L⟦(-1 : ℤ)⟧)

/-- The `n`th object of the shifted represented Hom tower is the group of maps
`K_n ⟶ L[-1]`. -/
@[simp]
theorem shiftedTower_obj (K : ℕ ⥤ D) (L : D) (n : ℕ) :
    (shiftedTower K L).obj (op n) = AddCommGrpCat.of (K.obj n ⟶ L⟦(-1 : ℤ)⟧) := sorry

/-- A transition in the shifted represented Hom tower is precomposition with the corresponding
map of the sequential diagram. -/
@[simp]
theorem shiftedTower_transitionMap_apply (K : ℕ ⥤ D) (L : D) {i j : ℕ}
    (hij : i ≤ j) (f : K.obj j ⟶ L⟦(-1 : ℤ)⟧) :
    (shiftedTower K L).transitionMap hij f = K.map (homOfLE hij) ≫ f := sorry

/-- The shift of a target morphism gives a morphism of shifted represented Hom towers. -/
@[stacks 0CQX]
abbrev shiftedTowerMap (K : ℕ ⥤ D) {L M : D} (f : L ⟶ M) :
    shiftedTower K L ⟶ shiftedTower K M :=
  towerMap K ((shiftFunctor D (-1 : ℤ)).map f)

/-- The component of `shiftedTowerMap` is induced by the shifted target morphism. -/
@[simp]
theorem shiftedTowerMap_app (K : ℕ ⥤ D) {L M : D} (f : L ⟶ M) (n : ℕ) :
    (shiftedTowerMap K f).app (op n) =
      (preadditiveYoneda.map ((shiftFunctor D (-1 : ℤ)).map f)).app
        (op (K.obj n)) := sorry

/-- On elements, `shiftedTowerMap` is postcomposition with the shifted target morphism. -/
@[simp]
theorem shiftedTowerMap_app_apply (K : ℕ ⥤ D) {L M : D} (f : L ⟶ M)
    (n : ℕ) (g : K.obj n ⟶ L⟦(-1 : ℤ)⟧) :
    (shiftedTowerMap K f).app (op n) g =
      g ≫ (shiftFunctor D (-1 : ℤ)).map f := sorry

/-- The identity target morphism induces the identity morphism of shifted represented Hom
towers. -/
@[simp, stacks 0CQX]
theorem shiftedTowerMap_id (K : ℕ ⥤ D) (L : D) :
    shiftedTowerMap K (𝟙 L) = 𝟙 (shiftedTower K L) := sorry

/-- Composition of target morphisms agrees with composition of their induced shifted
represented Hom tower morphisms. -/
@[simp, stacks 0CQX]
theorem shiftedTowerMap_comp (K : ℕ ⥤ D) {L M N : D} (f : L ⟶ M) (g : M ⟶ N) :
    shiftedTowerMap K (f ≫ g) = shiftedTowerMap K f ≫ shiftedTowerMap K g := sorry

variable (K : ℕ ⥤ D) in
/-- The shifted represented Hom tower as a functor of its unshifted target. -/
@[stacks 0CQX]
def shiftedTowerFunctor : D ⥤ SequentialInverseSystem AddCommGrpCat where
  obj := shiftedTower K
  map := shiftedTowerMap K
  map_id := shiftedTowerMap_id K
  map_comp := shiftedTowerMap_comp K

/-- The shifted target functor evaluates to the shifted represented Hom tower. -/
@[simp]
theorem shiftedTowerFunctor_obj (K : ℕ ⥤ D) (L : D) :
    (shiftedTowerFunctor K).obj L = shiftedTower K L := sorry

/-- The shifted target functor sends a morphism to `shiftedTowerMap`. -/
@[simp]
theorem shiftedTowerFunctor_map (K : ℕ ⥤ D) {L M : D} (f : L ⟶ M) :
    (shiftedTowerFunctor K).map f = shiftedTowerMap K f := sorry

end Shift

end CategoryTheory.HomotopyColimit.RepresentedHom

end
