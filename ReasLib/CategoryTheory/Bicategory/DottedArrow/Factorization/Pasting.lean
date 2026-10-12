/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Groupoid
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Factorization.RightFactor
public import ReasLib.CategoryTheory.Functor.MappingPath.InGroupoids

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

section CompositionPasting

variable {B : Type u} [Bicategory.{w, v} B] [Bicategory.IsLocallyGroupoid B]
variable {S T X Y Z : B}
variable (x : S ⟶ X) (j : S ⟶ T) (f : X ⟶ Y) (g : Y ⟶ Z) (z : T ⟶ Z)
variable (γ : j ≫ z ≅ x ≫ f ≫ g)

namespace DottedArrowPasting

/-
The source diagram and its two factored squares are

                              x                          f
                   S ─────────────────▶ X ─────────────────────────▶ Y
                   │                                                │
                 j │                                                │ g
                   ▼                                                ▼
                   T ─────────────────────── z ─────────────────────▶ Z
                   T ┈┈┈┈┈┈ dotted outer arrow ┈┈┈┈┈┈┈▶ X

                              x ≫ f
                   S ──────────────────────────────────────────────▶ Y
                   │                                                │
                 j │                                                │ g
                   ▼                                                ▼
                   T ─────────────────────── z ─────────────────────▶ Z
                   T ┈┈┈┈ dotted middle arrow d.arrow ┈┈┈┈┈┈┈┈▶ Y

                              x
                   S ─────────────────▶ X
                   │                    │
                 j │                    │ f
                   ▼                    ▼
                   T ─────────────────▶ Y
                           d.arrow
                   T ┈┈┈┈┈┈ dotted left arrow ┈┈┈┈┈┈┈┈▶ X

The chosen outer comparison is γ : j ≫ z ≅ x ≫ f ≫ g. The middle comparison is γ followed by
the inverse associator, and the left comparison is d.left.
-/

/-- The outer `2`-commutative rectangle associated to a composable pair of right edges. -/
def outerSquare :
    Bicategory.PseudoPullbackCone z (f ≫ g) where
  pt := S
  fst := j
  snd := x
  iso := γ

/-- The middle square obtained by factoring the right edge f ≫ g of outerSquare. -/
def middleSquare :
    Bicategory.PseudoPullbackCone z g :=
  Bicategory.PseudoPullbackCone.factorRight (outerSquare x j f g z γ)

/-- The left square determined by a fixed middle dotted arrow. -/
def leftSquare (d : DottedArrow (middleSquare x j f g z γ)) :
    Bicategory.PseudoPullbackCone d.arrow f :=
  DottedArrow.leftFactorSquare (outerSquare x j f g z γ) d

/-- The canonical functor from outer dotted arrows to middle dotted arrows. -/
def outerToMiddle :
    DottedArrow (outerSquare x j f g z γ) ⥤
      DottedArrow (middleSquare x j f g z γ) :=
  DottedArrow.factorRightFunctor (outerSquare x j f g z γ)

/-- The canonical comparison from outer dotted arrows to their mapping-path factorizations. -/
def outerComparison :
    DottedArrow (outerSquare x j f g z γ) ⥤
      Functor.MappingPath (outerToMiddle x j f g z γ) :=
  Functor.MappingPath.inclusion (outerToMiddle x j f g z γ)

/-- The category of outer dotted arrows is equivalent to the mapping-path
factorization category D''.

Proof strategy: specialize Functor.MappingPath.inclusionIsEquivalence to outerToMiddle. -/
@[stacks 0H1B "(1) outer comparison"]
instance outerComparison.isEquivalence :
    (outerComparison x j f g z γ).IsEquivalence := sorry

end DottedArrowPasting

end CompositionPasting

end CategoryTheory
