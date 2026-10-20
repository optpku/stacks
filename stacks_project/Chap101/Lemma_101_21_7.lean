/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.DeligneMumford.TwoFibreProduct
import StacksCheckRecall

/-!
# Étale scheme atlases of 2-fibre products along DM morphisms

If `f : X ⟶ Y` is a DM morphism of algebraic stacks, then a 2-fibre product of
`f` with a morphism from a DM algebraic stack (and, as a special case, from an
algebraic space) admits a scheme and a surjective étale morphism from that
scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

/- Lemma 101.21.7 (1): If `f : X ⟶ Y` is a DM morphism of algebraic stacks,
then for every DM algebraic stack `Z` and morphism `g : Z ⟶ Y` there exists a
scheme `U` and a surjective étale morphism
`GroupoidsOver.slice U ⟶ TwoFibreProduct.apex f g`.

Stacks writes `U ⟶ X ×_Y Z`; the Lean atlas is a slice 1-morphism into
`TwoFibreProduct.apex f g`. -/
@[stacks 0CIA]
#check (AlgebraicGeometry.AlgebraicStack.DM.exists_etale_surjective_twoFibreProduct :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.DM f] [AlgebraicStack.IsDM Z],
    ∃ (U : Over S)
      (p : GroupoidsOver.slice U ⟶
        TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p)

/- Lemma 101.21.7 (2): If `f : X ⟶ Y` is a DM morphism of algebraic stacks,
then for every algebraic space `Z` and morphism `g : Z.toGroupoids ⟶ Y` there
exists a scheme `U` and a surjective étale morphism
`GroupoidsOver.slice U ⟶ TwoFibreProduct.apex f g`.

Stacks writes `U ⟶ X ×_Y Z`; the Lean atlas is a slice 1-morphism into
`TwoFibreProduct.apex f g`. -/
@[stacks 0CIA]
#check (AlgebraicGeometry.AlgebraicStack.DM.exists_etale_surjective_twoFibreProduct_algebraicSpace :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (g : Z.toGroupoids ⟶ Y) [AlgebraicStack.DM f],
    ∃ (U : Over S)
      (p : GroupoidsOver.slice U ⟶
        TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p)

/- The 2-fibre product of a DM morphism of algebraic stacks with a morphism
from a DM algebraic stack is itself DM. -/
#check (AlgebraicGeometry.AlgebraicStack.IsDM.instTwoFibreProduct :
    ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [AlgebraicStack.DM f] [AlgebraicStack.IsDM Z],
    AlgebraicStack.IsDM (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g))
