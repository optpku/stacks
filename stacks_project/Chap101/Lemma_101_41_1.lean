/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_41_1_Comparison
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
#check (ValuativeCommSq.ofDiagonal sq : ValuativeCommSq f)

@[stacks 0E8L]
#check (ValuativeCommSq.fstDottedArrow sq :
  DottedArrow (ValuativeCommSq.ofDiagonal sq).toCone)

@[stacks 0E8L]
#check (ValuativeCommSq.sndDottedArrow sq :
  DottedArrow (ValuativeCommSq.ofDiagonal sq).toCone)

/- Lemma 101.41.1 (2): the dotted-arrow category of the original square is a
setoid whose isomorphism classes of objects are the morphisms
(a₁, α₁, id) ⟶ (a₂, α₂, φ) in the associated dotted-arrow category. -/
@[stacks 0E8L]
#check (ValuativeCommSq.isoClassEquiv sq :
  isomorphismClasses.obj (Cat.of (DottedArrow sq.toCone)) ≃
    (ValuativeCommSq.fstDottedArrow sq ⟶ ValuativeCommSq.sndDottedArrow sq))
