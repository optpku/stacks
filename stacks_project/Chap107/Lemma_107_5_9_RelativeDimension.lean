/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeDimension
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

#check (AlgebraicGeometry.AlgebraicStack.relativeDimensionAt :
    ∀ {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    (f : T ⟶ X) [LocallyOfFiniteType f] (t : Points T),
    EInt)

#check (AlgebraicGeometry.AlgebraicStack.relativeDimensionAt_eq :
    ∀ {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    (f : T ⟶ X) [LocallyOfFiniteType f] (t : Points T)
    (p : FieldValuedPoint X) (hp : Points.mk p = Points.map f t)
    (c : PseudoPullbackCone f p.hom) [AlgebraicStack c.pt]
    [IsLocallyNoetherian c.pt] (hc : c.IsBilimit) (tFiber : Points c.pt)
    (ht : Points.map c.fst tFiber = t),
    relativeDimensionAt f t = dimensionAt tFiber)

#check (AlgebraicGeometry.AlgebraicStack.relativeDimensionAt_spec :
    ∀ {S : Scheme.{u}} {T X : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X]
    (f : T ⟶ X) [LocallyOfFiniteType f] (t : Points T),
    ∃ (p : FieldValuedPoint X) (c : PseudoPullbackCone f p.hom)
      (hStack : AlgebraicStack c.pt) (hLN : @IsLocallyNoetherian S c.pt hStack)
      (hc : c.IsBilimit) (tFiber : @Points S c.pt hStack),
      Points.mk p = Points.map f t ∧
        @Points.map S c.pt hStack T inferInstance c.fst tFiber = t ∧
        relativeDimensionAt f t = @dimensionAt S c.pt hStack hLN tFiber)

end AlgebraicGeometry.AlgebraicStack
