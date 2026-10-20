/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.RelativeDimension
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open Bicategory
open scoped Bicategory

universe u

/- Definition 107.5.7: if `f : T ⟶ X` is a locally of finite type morphism
between locally Noetherian algebraic stacks, and `t ∈ |T|` is a point with
image `x ∈ |X|`, the relative dimension `dim_t(T_x)` is
`relativeDimensionAt f t`, equal to `dimensionAt t'` for a point `t'` of
`T ×_X Spec k` mapping to `t`. -/
@[stacks 0DRL] #check (AlgebraicGeometry.AlgebraicStack.relativeDimensionAt :
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
