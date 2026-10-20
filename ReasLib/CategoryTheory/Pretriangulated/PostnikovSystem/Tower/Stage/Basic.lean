/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Category

/-!
# Structural Stage Functors of Sequential Postnikov Towers

This file exposes row and auxiliary evaluations and the differential, comparison,
second, and connecting maps of sequential Postnikov towers as functorial data.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower.Stage

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

variable (D) in
/-- Evaluation of a sequential Postnikov tower at its `n`th row object `Xₙ`. -/
@[stacks 0D8Z "row-object evaluation of sequential Postnikov towers"]
def row (n : ℕ) : Tower D ⥤ D where
  obj T := T.X n
  map f := f.xMap n
  map_id := sorry
  map_comp := sorry

/-- Row-object evaluation returns the corresponding object of the tower. -/
@[simp, stacks 0D8Z]
theorem row_obj (n : ℕ) (T : Tower D) :
    (row D n).obj T = T.X n := sorry

/-- Row-object evaluation maps a tower morphism by its corresponding `xMap` component. -/
@[simp, stacks 0D8Z]
theorem row_map (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    (row D n).map f = f.xMap n := sorry

variable (D) in
/-- Evaluation of a sequential Postnikov tower at its `n`th auxiliary object `Yₙ`. -/
@[stacks 0D8Z "auxiliary-object evaluation of sequential Postnikov towers"]
def aux (n : ℕ) : Tower D ⥤ D where
  obj T := T.Y n
  map f := f.yMap n
  map_id := sorry
  map_comp := sorry

/-- Auxiliary-object evaluation returns the corresponding object of the tower. -/
@[simp, stacks 0D8Z]
theorem aux_obj (n : ℕ) (T : Tower D) :
    (aux D n).obj T = T.Y n := sorry

/-- Auxiliary-object evaluation maps a tower morphism by its corresponding `yMap` component. -/
@[simp, stacks 0D8Z]
theorem aux_map (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    (aux D n).map f = f.yMap n := sorry

/-- Naturality of the differentials between consecutive row-object evaluations. -/
@[reassoc, stacks 0D8Z]
theorem d_naturality (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    f.xMap (n + 1) ≫ T'.d n = T.d n ≫ f.xMap n := sorry

variable (D) in
/-- The differentials of sequential Postnikov towers as a natural transformation between
consecutive row-object evaluations. -/
@[stacks 0D8Z "differential of sequential Postnikov towers"]
def d (n : ℕ) : row D (n + 1) ⟶ row D n where
  app T := T.d n
  naturality _ _ f := d_naturality n f

/-- The component of the differential natural transformation is the tower differential. -/
@[simp, stacks 0D8Z]
theorem d_app (n : ℕ) (T : Tower D) :
    (d D n).app T = T.d n := sorry

/-- Naturality of the comparison from auxiliary objects to row objects. -/
@[reassoc, stacks 0D8Z]
theorem toX_naturality (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    f.yMap n ≫ T'.toX n = T.toX n ≫ f.xMap n := sorry

variable (D) in
/-- The comparisons `Yₙ ⟶ Xₙ` as a natural transformation of sequential Postnikov towers. -/
@[stacks 0D8Z "auxiliary-to-row comparison of sequential Postnikov towers"]
def toX (n : ℕ) : aux D n ⟶ row D n where
  app T := T.toX n
  naturality _ _ f := toX_naturality n f

/-- The component of the auxiliary-to-row comparison is the corresponding tower map. -/
@[simp, stacks 0D8Z]
theorem toX_app (n : ℕ) (T : Tower D) :
    (toX D n).app T = T.toX n := sorry

/-- Naturality of the second maps of sequential Postnikov stage triangles. -/
@[reassoc, stacks 0D8Z]
theorem toNext_naturality (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    f.xMap (n + 1) ≫ T'.toNext n = T.toNext n ≫ f.yMap n := sorry

variable (D) in
/-- The second maps `Xₙ₊₁ ⟶ Yₙ` as a natural transformation of sequential Postnikov towers. -/
@[stacks 0D8Z "second map of sequential Postnikov stage triangles"]
def toNext (n : ℕ) : row D (n + 1) ⟶ aux D n where
  app T := T.toNext n
  naturality _ _ f := toNext_naturality n f

/-- The component of the second-map natural transformation is the corresponding tower map. -/
@[simp, stacks 0D8Z]
theorem toNext_app (n : ℕ) (T : Tower D) :
    (toNext D n).app T = T.toNext n := sorry

/-- Naturality of the connecting maps of sequential Postnikov stage triangles. -/
@[reassoc, stacks 0D8Z]
theorem connecting_naturality (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    f.yMap n ≫ T'.connecting n =
      T.connecting n ≫ (shiftFunctor D (1 : ℤ)).map (f.yMap (n + 1)) := sorry

variable (D) in
/-- The connecting maps `Yₙ ⟶ Yₙ₊₁[1]` as a natural transformation of sequential Postnikov
towers. -/
@[stacks 0D8Z "connecting map of sequential Postnikov stage triangles"]
def connecting (n : ℕ) :
    aux D n ⟶ aux D (n + 1) ⋙ shiftFunctor D (1 : ℤ) where
  app T := T.connecting n
  naturality _ _ f := connecting_naturality n f

/-- The component of the connecting natural transformation is the corresponding tower map. -/
@[simp, stacks 0D8Z]
theorem connecting_app (n : ℕ) (T : Tower D) :
    (connecting D n).app T = T.connecting n := sorry

end CategoryTheory.PostnikovSystem.Tower.Stage
