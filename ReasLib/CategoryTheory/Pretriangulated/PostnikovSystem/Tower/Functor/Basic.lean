/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Category
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Morphism.Finite.Functoriality

/-!
# Finite Restriction Functors for Postnikov Towers

This leaf owns the finite-row and finite-system restriction functors of a
sequential Postnikov tower, together with their object and morphism computation
API.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

variable (D) in
/-- Restriction of a sequential Postnikov tower to its reversed row of length `n`. -/
@[stacks 0D8Z "finite-row restriction functor for Postnikov towers"]
def rowFunctor (n : ℕ) : Tower D ⥤ ComposableArrows D n where
  obj T := T.row n
  map f := Hom.row f n
  map_id T := Hom.id_row T n
  map_comp f g := Hom.comp_row f g n

/-- The object map of `rowFunctor` is finite-row restriction. -/
@[simp, stacks 0D8Z]
theorem rowFunctor_obj (n : ℕ) (T : Tower D) :
    (rowFunctor D n).obj T = T.row n := sorry

/-- The morphism map of `rowFunctor` is restriction of a tower morphism to a finite row. -/
@[simp, stacks 0D8Z]
theorem rowFunctor_map (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    (rowFunctor D n).map f = Hom.row f n := sorry

variable (D) in
/-- Restriction of a sequential Postnikov tower to its finite Postnikov system, retaining the
underlying finite row in the total category. -/
@[stacks 0D8Z "finite-system restriction functor for Postnikov towers"]
def finiteFunctor (n : ℕ) : Tower D ⥤ PostnikovSystem.Total D n where
  obj T :=
    { base := T.row n
      system := T.finite n }
  map f :=
    { base := Hom.row f n
      systemMap := Hom.finite f n }
  map_id := sorry
  map_comp := sorry

/-- The base of the object selected by `finiteFunctor` is the finite row. -/
@[simp, stacks 0D8Z]
theorem finiteFunctor_obj_base (n : ℕ) (T : Tower D) :
    ((finiteFunctor D n).obj T).base = T.row n := sorry

/-- The system carried by the object selected by `finiteFunctor` is the finite restriction. -/
@[simp, stacks 0D8Z]
theorem finiteFunctor_obj_system (n : ℕ) (T : Tower D) :
    ((finiteFunctor D n).obj T).system = T.finite n := sorry

/-- The base component of `finiteFunctor.map` is finite-row restriction of the tower morphism. -/
@[simp, stacks 0D8Z]
theorem finiteFunctor_map_base (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    ((finiteFunctor D n).map f).base = Hom.row f n := sorry

/-- The system component of `finiteFunctor.map` is finite restriction of the tower morphism. -/
@[simp, stacks 0D8Z]
theorem finiteFunctor_map_systemMap (n : ℕ) {T T' : Tower D} (f : T ⟶ T') :
    ((finiteFunctor D n).map f).systemMap = Hom.finite f n := sorry

end CategoryTheory.PostnikovSystem.Tower
