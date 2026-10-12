/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Forget

/-!
# Evaluation of Total Finite Postnikov Systems

This leaf exposes the underlying-row and auxiliary-object evaluation functors,
together with the canonical natural transformation from auxiliary objects to
the finite row.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]
variable {n : ℕ}

variable (D) in
/-- Evaluation of the underlying finite row at `i`. This is the ordinary functor-category
evaluation after forgetting the Postnikov-system data. -/
@[stacks 0D7Z "evaluation of an underlying Postnikov row"]
def row (n : ℕ) (i : Fin (n + 1)) : Total D n ⥤ D :=
  forget D n ⋙ (evaluation (Fin (n + 1)) D).obj i

variable (D) in
/-- Evaluation of an underlying row is definitionally obtained by composing `forget` with the
ordinary evaluation functor. -/
@[stacks 0D7Z "underlying-row evaluation through forget"]
theorem row_eq (n : ℕ) (i : Fin (n + 1)) :
    row D n i = forget D n ⋙ (evaluation (Fin (n + 1)) D).obj i := sorry

/-- Evaluating the underlying row of a total object returns its `i`th row object. -/
@[simp, stacks 0D7Z "underlying-row evaluation on objects"]
theorem row_obj (i : Fin (n + 1)) (P : Total D n) :
    (row D n i).obj P = P.base.obj i := sorry

/-- Evaluating a total morphism on the underlying row returns the `i`th component of its base
map. -/
@[simp, stacks 0D7Z "underlying-row evaluation on morphisms"]
theorem row_map (i : Fin (n + 1)) {P Q : Total D n} (f : P ⟶ Q) :
    (row D n i).map f = f.base.app i := sorry

variable (D) in
/-- Evaluation of a finite Postnikov system at its `i`th auxiliary `Y` object. -/
@[stacks 0D7Z "evaluation of a Postnikov auxiliary object"]
def aux (n : ℕ) (i : Fin (n + 1)) : Total D n ⥤ D where
  obj P := P.system i
  map f := f.systemMap.yMap i
  map_id P := id_yMap P i
  map_comp f g := comp_yMap f g i

/-- Evaluating a total object at `i` returns the `i`th auxiliary `Y` object of its Postnikov
system. -/
@[simp, stacks 0D7Z "auxiliary evaluation on objects"]
theorem aux_obj (i : Fin (n + 1)) (P : Total D n) :
    (aux D n i).obj P = P.system i := sorry

/-- Evaluating a total morphism on auxiliary objects returns its `i`th `yMap` component. -/
@[simp, stacks 0D7Z "auxiliary evaluation on morphisms"]
theorem aux_map (i : Fin (n + 1)) {P Q : Total D n} (f : P ⟶ Q) :
    (aux D n i).map f = f.systemMap.yMap i := sorry

/-- The comparison maps from auxiliary objects to row objects are natural in a total
Postnikov-system morphism. -/
@[reassoc, stacks 0D7Z "naturality of auxiliary-to-row comparison"]
theorem toRow_naturality (i : Fin (n + 1)) {P Q : Total D n} (f : P ⟶ Q) :
    f.systemMap.yMap i ≫ Q.system.toX i = P.system.toX i ≫ f.base.app i := sorry

variable (D) in
/-- The stagewise comparison from the auxiliary-object evaluation functor to the underlying-row
evaluation functor. -/
@[stacks 0D7Z "auxiliary-to-row comparison"]
def toRow (n : ℕ) (i : Fin (n + 1)) : aux D n i ⟶ row D n i where
  app P := P.system.toX i
  naturality _ _ f := toRow_naturality i f

/-- The component of `toRow` is the comparison from the selected auxiliary object to the
corresponding row object. -/
@[simp, stacks 0D7Z "auxiliary-to-row comparison component"]
theorem toRow_app (i : Fin (n + 1)) (P : Total D n) :
    (toRow D n i).app P = P.system.toX i := sorry

end CategoryTheory.PostnikovSystem.Total
