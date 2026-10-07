module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic
public import stacks_project.Chap100.Definition_100_12_3_Dimension
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType

/-!
# Relative dimension of morphisms of algebraic stacks

The relative dimension of a locally of finite type morphism of locally
Noetherian algebraic stacks at a point is the dimension of any field-valued
2-fibre through that point, valued in `EInt` so that it may be negative.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The relative dimension of a locally of finite type morphism `f : T ⟶ X` of
locally Noetherian algebraic stacks at a point `t` of `|T|`, as the supremum of
`dimensionAt` along field-valued 2-fibre lifts of `t`. -/
noncomputable def relativeDimensionAt {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    (f : T ⟶ X) [LocallyOfFiniteType f] (t : Points T) : EInt :=
  ⨆ (p : FieldValuedPoint X) (_hp : Points.mk p = Points.map f t)
      (c : PseudoPullbackCone f p.hom) (hStack : AlgebraicStack c.pt)
      (hLN : @IsLocallyNoetherian S c.pt hStack) (_hc : c.IsBilimit)
      (tFiber : @Points S c.pt hStack)
      (_ht : @Points.map S c.pt hStack T inferInstance c.fst tFiber = t),
    @dimensionAt S c.pt hStack hLN tFiber

/-- The relative dimension of `f` at `t` equals the dimension at any lift of `t`
to a field-valued bilimit 2-fibre of `f`. -/
theorem relativeDimensionAt_eq {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    (f : T ⟶ X) [LocallyOfFiniteType f] (t : Points T)
    (p : FieldValuedPoint X) (hp : Points.mk p = Points.map f t)
    (c : PseudoPullbackCone f p.hom) [AlgebraicStack c.pt]
    [IsLocallyNoetherian c.pt] (hc : c.IsBilimit) (tFiber : Points c.pt)
    (ht : Points.map c.fst tFiber = t) :
    relativeDimensionAt f t = dimensionAt tFiber :=
  sorry

/-- The relative dimension of `f` at `t` is the dimension at some lift of `t` to
a field-valued 2-fibre `T ×_X Spec k` representing the image of `t`. -/
theorem relativeDimensionAt_spec {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    (f : T ⟶ X) [LocallyOfFiniteType f] (t : Points T) :
    ∃ (p : FieldValuedPoint X) (c : PseudoPullbackCone f p.hom)
      (hStack : AlgebraicStack c.pt) (hLN : @IsLocallyNoetherian S c.pt hStack)
      (hc : c.IsBilimit) (tFiber : @Points S c.pt hStack),
      Points.mk p = Points.map f t ∧
        @Points.map S c.pt hStack T inferInstance c.fst tFiber = t ∧
        relativeDimensionAt f t = @dimensionAt S c.pt hStack hLN tFiber :=
  sorry

/-- Relative dimension is invariant along the projections of a chosen 2-fibre
product of locally Noetherian algebraic stacks, once the apex is algebraic and
locally Noetherian and the second projection is locally of finite type. -/
theorem relativeDimensionAt_eq_of_twoFibreProduct {S : Scheme.{u}}
    {T X X' : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack X']
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian X']
    (f : T ⟶ X) [LocallyOfFiniteType f] (g : X' ⟶ X)
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [IsLocallyNoetherian (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)]
    [LocallyOfFiniteType (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)]
    (t' : Points (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)) :
    relativeDimensionAt (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g) t' =
      relativeDimensionAt f
        (Points.map (TwoFibreProduct.fst.{u + 1, u, u + 1, u} f g) t') :=
  sorry

end AlgebraicGeometry.AlgebraicStack
