module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.DeligneMumford.Characterization
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Transfer

/-!
# Deligne-Mumford 2-fibre products and their étale scheme atlases

The base change of a DM morphism by a DM algebraic stack is DM and admits a
surjective étale scheme atlas. In particular, this holds for base change by
an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.IsDM

/-- The 2-fibre product of a DM morphism of algebraic stacks with a morphism
from a DM algebraic stack is itself DM. -/
instance instTwoFibreProduct {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [DM f] [IsDM Z] :
    IsDM (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.IsDM

namespace AlgebraicGeometry.AlgebraicStack.DM

/-- The base change of a DM morphism of algebraic stacks by a morphism from
a DM algebraic stack admits a surjective étale morphism from a scheme. -/
theorem exists_etale_surjective_twoFibreProduct
    {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y) [DM f] [IsDM Z] :
    ∃ (U : Over S)
      (p : GroupoidsOver.slice U ⟶
        TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p :=
  sorry

/-- The base change of a DM morphism of algebraic stacks by a morphism from
an algebraic space admits a surjective étale morphism from a scheme. -/
theorem exists_etale_surjective_twoFibreProduct_algebraicSpace
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) {Z : AlgebraicSpace S}
    (g : Z.toGroupoids ⟶ Y) [DM f] :
    ∃ (U : Over S)
      (p : GroupoidsOver.slice U ⟶
        TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g),
      Groupoids.Hom.Etale p ∧ Groupoids.Hom.Surjective p :=
  sorry

end AlgebraicGeometry.AlgebraicStack.DM
