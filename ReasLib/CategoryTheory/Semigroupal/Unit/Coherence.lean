/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Semigroupal.Unit

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.SemigroupalCategory

variable {C : Type u} [Category.{v} C] [SemigroupalCategory C]

/-- The multiplication of a cancellable idempotent is its reconstructed left unitor
at the idempotent object. -/
theorem CategoryTheory.SemigroupalCategory.UnitSeed.mul_eq_leftUnitor (seed : UnitSeed C) :
    seed.mul.hom = (seed.leftUnitor.app seed.obj).hom := sorry

/-- The multiplication of a cancellable idempotent is its reconstructed right unitor
at the idempotent object. -/
theorem CategoryTheory.SemigroupalCategory.UnitSeed.mul_eq_rightUnitor (seed : UnitSeed C) :
    seed.mul.hom = (seed.rightUnitor.app seed.obj).hom := sorry

/-- The reconstructed left unitor commutes with tensoring on the right,
after reassociation. -/
theorem CategoryTheory.SemigroupalCategory.UnitSeed.leftUnitor_tensor (seed : UnitSeed C) (X Y : C) :
    (associator seed.obj X Y).hom ≫ (seed.leftUnitor.app (tensorObj X Y)).hom =
      whiskerRight ((seed.leftUnitor.app X).hom) Y := sorry

/-- The reconstructed right unitor commutes with tensoring on the left,
after reassociation. -/
theorem CategoryTheory.SemigroupalCategory.UnitSeed.rightUnitor_tensor (seed : UnitSeed C) (X Y : C) :
    (seed.rightUnitor.app (tensorObj X Y)).hom =
      (associator X Y seed.obj).hom ≫ whiskerLeft X ((seed.rightUnitor.app Y).hom) := sorry

/-- The associator of a coherent tensor satisfies the pentagon identity. -/
theorem CategoryTheory.SemigroupalCategory.pentagonIdentity :
    ∀ W X Y Z : C,
      tensor.map ⟨(associator W X Y).hom, 𝟙 Z⟩ ≫
          (associator W (tensor.obj (X, Y)) Z).hom ≫
          tensor.map ⟨𝟙 W, (associator X Y Z).hom⟩ =
        (associator (tensor.obj (W, X)) Y Z).hom ≫
          (associator W X (tensor.obj (Y, Z))).hom :=
  CategoryTheory.SemigroupalCategory.pentagon
