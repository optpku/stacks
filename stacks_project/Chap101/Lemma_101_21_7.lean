/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap94.Definition_94_12_2_Etale
public import stacks_project.Chap101.Definition_101_4_2_Separation

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

namespace AlgebraicGeometry.AlgebraicStack.DM

/-- Lemma 101.21.7 (1): If `f : X ⟶ Y` is a DM morphism of algebraic stacks,
then for every DM algebraic stack `Z` and morphism `g : Z ⟶ Y` there exists a
scheme `U` and a surjective étale morphism
`GroupoidsOver.slice U ⟶ TwoFibreProduct.apex f g`.

Stacks writes `U ⟶ X ×_Y Z`; the Lean atlas is a slice 1-morphism into
`TwoFibreProduct.apex f g`. -/
@[stacks 0CIA]
theorem exists_etale_surjective_twoFibreProduct
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [DM f] [IsDM Z]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    ∃ (U : Over S)
      (p : GroupoidsOver.slice U ⟶
        TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p :=
  sorry

/-- Lemma 101.21.7 (2): If `f : X ⟶ Y` is a DM morphism of algebraic stacks,
then for every algebraic space `Z` and morphism `g : Z.toGroupoids ⟶ Y` there
exists a scheme `U` and a surjective étale morphism
`GroupoidsOver.slice U ⟶ TwoFibreProduct.apex f g`.

Stacks writes `U ⟶ X ×_Y Z`; the Lean atlas is a slice 1-morphism into
`TwoFibreProduct.apex f g`. -/
@[stacks 0CIA]
theorem exists_etale_surjective_twoFibreProduct_algebraicSpace
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (g : Z.toGroupoids ⟶ Y) [DM f]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    ∃ (U : Over S)
      (p : GroupoidsOver.slice U ⟶
        TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p :=
  sorry

end AlgebraicGeometry.AlgebraicStack.DM

namespace AlgebraicGeometry.AlgebraicStack.IsDM

/-- The 2-fibre product of a DM morphism of algebraic stacks with a morphism
from a DM algebraic stack is itself DM. -/
instance instTwoFibreProduct {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [DM f] [IsDM Z]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    IsDM (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsDM
