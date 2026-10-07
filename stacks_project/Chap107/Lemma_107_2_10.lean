module

public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap107.Remark_107_2_9_Upgrading_versal_rings_Morphism
public import stacks_project.Chap107.Situation_107_2_1_Instances
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness of the morphism from a versal ring

In Situation 107.2.1, the morphism `Spec(A) ⟶ X` of Remark 107.2.9 attached to
a versal ring at a finite-type field-valued point is a flat morphism of
algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

set_option synthInstance.checkSynthOrder false in
/-- Lemma 107.2.10: In Situation 107.2.1 let `x0 : Spec(k) ⟶ X` be a morphism,
where `k` is a finite type field over `S`. Let `A` be a versal ring to `X` at
`x0`. Then the morphism `Spec(A) ⟶ X` of Remark 107.2.9 is flat. -/
@[stacks 0DR2]
instance isFlat_yonedaOfObject {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A]
    (x : CompleteLocalObject X) (hx : RealizesVersalRing x0 A x) :
    let _ := hx
    Flat (yonedaOfObject x.base.toS x.object x.over_obj) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
