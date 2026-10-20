/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit

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
  ⨆ (p : FieldValuedPoint X) (hp : Points.mk p = Points.map f t)
      (c : PseudoPullbackCone f p.hom) (hStack : AlgebraicStack c.pt)
      (hLN : @IsLocallyNoetherian S c.pt hStack) (hc : c.IsBilimit)
      (tFiber : @Points S c.pt hStack)
      (ht : @Points.map S c.pt hStack T inferInstance c.fst tFiber = t),
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

/-- In a Cartesian square of locally Noetherian algebraic stacks with locally
of finite type vertical morphisms, relative dimension at a point of the upper
left stack equals relative dimension at its image in the upper right stack. -/
theorem relativeDimensionAt_eq_of_isBilimit {S : Scheme.{u}}
    {T X T' X' : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack T'] [AlgebraicStack X']
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    [IsLocallyNoetherian T'] [IsLocallyNoetherian X']
    {f : T ⟶ X} {g : X' ⟶ X} {g' : T' ⟶ T} {f' : T' ⟶ X'}
    [LocallyOfFiniteType f] [LocallyOfFiniteType f']
    (iso : g' ≫ f ≅ f' ≫ g) (h : (PseudoPullbackCone.mk f g T' g' f' iso).IsBilimit)
    (t' : Points T') :
    relativeDimensionAt f' t' = relativeDimensionAt f (Points.map g' t') :=
  sorry

end AlgebraicGeometry.AlgebraicStack
