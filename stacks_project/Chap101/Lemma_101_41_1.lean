/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.ValuativeCriterion.Diagonal
import StacksCheckRecall

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]
variable {f : X ⟶ Y}
variable (sq : ValuativeCommSq (Hom.diagonal.{u + 1, u, u + 1} f))

/- Lemma 101.41.1 (1): a valuative 2-square of Hom.diagonal f yields an associated
valuative square of f with bottom f ∘ a₁, together with dotted arrows
(a₁, α₁, id) and (a₂, α₂, φ). -/
@[stacks 0E8L]
#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.ofDiagonal sq : ValuativeCommSq f)

/- Lemma 101.41.1 (1): the first distinguished dotted arrow has components (a₁, α₁, id). -/
@[stacks 0E8L]
#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.fstDottedArrow sq :
  DottedArrow (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.ofDiagonal sq).toCone)

/- Lemma 101.41.1 (1): the second distinguished dotted arrow has components (a₂, α₂, φ). -/
@[stacks 0E8L]
#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.sndDottedArrow sq :
  DottedArrow (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.ofDiagonal sq).toCone)

/- Lemma 101.41.1 (2): the original dotted-arrow category is thin. -/
@[stacks 0E8L]
#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.dottedArrow_isThin sq :
  Quiver.IsThin (DottedArrow sq.toCone))

/- Lemma 101.41.1 (2): the dotted-arrow category of the original square is a
setoid whose isomorphism classes of objects are the morphisms
(a₁, α₁, id) ⟶ (a₂, α₂, φ) in the associated dotted-arrow category. -/
@[stacks 0E8L]
#check (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.isoClassEquiv sq :
  isomorphismClasses.obj (Cat.of (DottedArrow sq.toCone)) ≃
    (AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.fstDottedArrow sq ⟶
      AlgebraicGeometry.AlgebraicStack.ValuativeCommSq.sndDottedArrow sq))
