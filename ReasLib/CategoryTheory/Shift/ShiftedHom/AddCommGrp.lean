module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Shift.ShiftedHom
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Shifted Morphism Groups as Additive Category Objects

This leaf bundles shifted morphism groups in `AddCommGrpCat` and exposes their functoriality in
both variables. It is independent of derived categories and Ext spectral sequences.
-/

open CategoryTheory

universe v u

namespace CategoryTheory.ShiftedHom

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive]

/-- A shifted morphism group bundled as an object of `AddCommGrpCat`. -/
@[stacks 0G1X, stacks 0G1Y, stacks 0G1Z, stacks 0G20]
abbrev addCommGrp (X Y : C) (n : ℤ) : AddCommGrpCat.{v} :=
  AddCommGrpCat.of (ShiftedHom X Y n)

/-- Precomposition is additive on shifted morphism groups. -/
theorem precomp_add {X Y Z : C} (f : X ⟶ Y) (n : ℤ)
    (α β : ShiftedHom Y Z n) :
    f ≫ (α + β) = f ≫ α + f ≫ β := sorry

/-- Contravariant functoriality of shifted morphism groups in the source. -/
@[stacks 0G1X, stacks 0G1Z]
def precomp {X Y : C} (f : X ⟶ Y) (Z : C) (n : ℤ) :
    addCommGrp Y Z n ⟶ addCommGrp X Z n :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk' (fun α ↦ f ≫ α) (precomp_add f n)

/-- Postcomposition after shifting is additive on shifted morphism groups. -/
theorem postcomp_add (X : C) {Y Z : C} (f : Y ⟶ Z) (n : ℤ)
    (α β : ShiftedHom X Y n) :
    (α + β) ≫ (shiftFunctor C n).map f =
      α ≫ (shiftFunctor C n).map f + β ≫ (shiftFunctor C n).map f := sorry

/-- Covariant functoriality of shifted morphism groups in the target. -/
@[stacks 0G1X, stacks 0G1Z]
def postcomp (X : C) {Y Z : C} (f : Y ⟶ Z) (n : ℤ) :
    addCommGrp X Y n ⟶ addCommGrp X Z n :=
  AddCommGrpCat.ofHom <|
    AddMonoidHom.mk' (fun α ↦ α ≫ (shiftFunctor C n).map f) (postcomp_add X f n)

end CategoryTheory.ShiftedHom
