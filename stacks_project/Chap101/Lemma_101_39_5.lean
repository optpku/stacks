module

public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Valuation.ValuationRing
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Factorization.Pasting
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
import StacksCheckRecall

/-!
# Composition of dotted-arrow categories for algebraic stacks

The category of dotted arrows for a 2-commutative valuative ladder of algebraic
stacks is a special case of the bicategorical pasting/factorization calculus:
the outer dotted-arrow category is equivalent to a mapping-path category fibred
in groupoids over the middle dotted-arrow category, with fibres the left
dotted-arrow categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids (overMap)
open DottedArrowPasting
open DottedArrow.Factorization
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
variable {A K : Type u} [CommRing A] [IsDomain A] [ValuationRing A] [Field K]
variable [Algebra A K] [IsFractionRing A K]
variable (hA : Spec (.of A) ⟶ S) (f : X ⟶ Y) (g : Y ⟶ Z)
variable
  (x : GroupoidsOver.slice (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ hA)) ⟶ X)
  (z : GroupoidsOver.slice (Over.mk hA) ⟶ Z)
  (γ : overMap (Over.homMk
      (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ hA))
      (V := Over.mk hA)
    (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl) ≫ z ≅
    x ≫ f ≫ g)
variable (d : DottedArrow (middleSquare x
  (overMap (Over.homMk
      (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ hA))
      (V := Over.mk hA)
    (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl)) f g z γ))

-- Here j is the canonical slice map induced by Spec.map (algebraMap A K),
-- C is DottedArrow of the outer square, C' is DottedArrow of the middle square,
-- and C'' is MappingPath of outerToMiddle.

/- Lemma 101.39.5 (1): the category C of outer dotted arrows for the valuative
rectangle Spec(K) ⟶ X ⟶ Y ⟶ Z over Spec(A) ⟶ Z, with 2-iso γ, is equivalent
to the mapping-path category C''. -/
@[stacks 0CLF]
#check (CategoryTheory.DottedArrowPasting.outerComparison.isEquivalence x
  (overMap (Over.homMk
      (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ hA))
      (V := Over.mk hA)
    (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl)) f g z γ :
  (outerComparison x
    (overMap (Over.homMk
      (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ hA))
      (V := Over.mk hA)
      (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl))
    f g z γ).IsEquivalence)

/- Lemma 101.39.5 (2): the mapping-path projection C'' ⥤ C' is fibred in
groupoids, where C' is the middle dotted-arrow category for Spec(K) ⟶ Y ⟶ Z. -/
@[stacks 0CLF "(2)"]
#check (CategoryTheory.DottedArrow.Factorization.projectionInGroupoids (outerSquare x
  (overMap (Over.homMk
      (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ hA))
      (V := Over.mk hA)
    (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl)) f g z γ) :
  Functor.IsFibered.InGroupoids
    (projection (outerSquare x
      (overMap (Over.homMk
      (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ hA))
      (V := Over.mk hA)
        (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl)) f g z γ)))

/- Lemma 101.39.5 (3): the fibre of C'' ⥤ C' over a middle dotted arrow d is
isomorphic to the left dotted-arrow category for Spec(K) ⟶ X ⟶ Y with bottom
arrow d.arrow : Spec(A) ⟶ Y and 2-iso d.left : j ≫ d.arrow ≅ x ≫ f,
where j is the canonical slice map induced by Spec.map (algebraMap A K). -/
@[stacks 0CLF "(3)"]
#check (CategoryTheory.DottedArrow.Factorization.fiberComparison.isIso (outerSquare x
  (overMap (Over.homMk
      (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ hA))
      (V := Over.mk hA)
    (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl)) f g z γ) d :
  (fiberComparison (outerSquare x
    (overMap (Over.homMk
      (U := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ hA))
      (V := Over.mk hA)
      (Spec.map (CommRingCat.ofHom (algebraMap A K))) rfl)) f g z γ) d).IsIso)
end AlgebraicGeometry.AlgebraicStack
