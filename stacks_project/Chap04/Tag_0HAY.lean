/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Semigroupal.Unit.Coherence
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SemigroupalCategory

universe v u

variable {C : Type u} [Category.{v} C] [SemigroupalCategory C]

/- The first two entries jointly express source clause (1). Entries (3) and (4)
express source clauses (2) and (3), respectively. The pentagon and triangle in
entries (5) and (6) supply the final coherence assumptions. -/

/- Lemma (0HAY) (1). The chosen multiplication agrees with the reconstructed
left unitor at the unit object. -/
@[stacks 0HAY] #check (CategoryTheory.SemigroupalCategory.UnitSeed.mul_eq_leftUnitor :
  ∀ seed : UnitSeed C, seed.mul.hom = (seed.leftUnitor.app seed.obj).hom)

/- Lemma (0HAY) (2). The chosen multiplication agrees with the reconstructed
right unitor at the unit object. -/
@[stacks 0HAY] #check (CategoryTheory.SemigroupalCategory.UnitSeed.mul_eq_rightUnitor :
  ∀ seed : UnitSeed C, seed.mul.hom = (seed.rightUnitor.app seed.obj).hom)

/- Lemma (0HAY) (3). Removing the left unit commutes with tensoring on the right,
with the associator making the parenthesization explicit. -/
@[stacks 0HAY] #check (CategoryTheory.SemigroupalCategory.UnitSeed.leftUnitor_tensor :
  ∀ (seed : UnitSeed C) (X Y : C),
    (associator seed.obj X Y).hom ≫ (seed.leftUnitor.app (tensorObj X Y)).hom =
      whiskerRight ((seed.leftUnitor.app X).hom) Y)

/- Lemma (0HAY) (4). Removing the right unit commutes with tensoring on the left,
with the associator making the parenthesization explicit. -/
@[stacks 0HAY] #check (CategoryTheory.SemigroupalCategory.UnitSeed.rightUnitor_tensor :
  ∀ (seed : UnitSeed C) (X Y : C),
    (seed.rightUnitor.app (tensorObj X Y)).hom =
      (associator X Y seed.obj).hom ≫ whiskerLeft X ((seed.rightUnitor.app Y).hom))

/- Lemma (0HAY) (5). The coherent tensor satisfies the pentagon identity. -/
@[stacks 0HAY] #check (CategoryTheory.SemigroupalCategory.pentagonIdentity :
  ∀ W X Y Z : C,
    tensor.map ⟨(associator W X Y).hom, 𝟙 Z⟩ ≫
        (associator W (tensor.obj (X, Y)) Z).hom ≫
        tensor.map ⟨𝟙 W, (associator X Y Z).hom⟩ =
      (associator (tensor.obj (W, X)) Y Z).hom ≫
        (associator W X (tensor.obj (Y, Z))).hom)

/- Lemma (0HAY) (6). The reconstructed unitors satisfy the triangle identity. -/
@[stacks 0HAY] #check (CategoryTheory.SemigroupalCategory.Unit.ofSeed_triangle :
  ∀ (seed : UnitSeed C) (X Y : C),
    (associator X seed.obj Y).hom ≫ whiskerLeft X (seed.leftUnitor.hom.app Y) =
      whiskerRight (seed.rightUnitor.hom.app X) Y)
