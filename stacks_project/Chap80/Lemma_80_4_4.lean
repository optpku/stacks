/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import stacks_project.Chap73.Lemma_73_7_3_Precoverage
public import stacks_project.Chap80.Definition_80_4_1_Relative

/-!
# Products of transferred morphism properties of algebraic spaces

If a morphism property of algebraic spaces is as in Definition 80.4.1 and
stable under composition, then its transfer to morphisms of presheaves
representable by algebraic spaces is closed under binary products of maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 80.4.4: let `S` be a scheme. Let `P` be a property as in
Definition 80.4.1 (stable under base change and fppf local on the target),
and assume `P` is stable under composition. For maps `a₁ : F₁ ⟶ G₁` and
`a₂ : F₂ ⟶ G₂` of presheaves on `(Sch/S)_fppf` that are representable by
algebraic spaces and have `P`, the product morphism
`prod.map a₁ a₂ : F₁ ⨯ F₂ ⟶ G₁ ⨯ G₂` (Stacks `a₁ × a₂`) also has `P`. -/
@[stacks 046H]
theorem relativeAlgebraicSpaces.prod_map {S : Scheme.{u}}
    {P : MorphismProperty (AlgebraicSpace S)} [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (fppfPrecoverage S)] [P.IsStableUnderComposition]
    {F₁ F₂ G₁ G₂ : (Over S)ᵒᵖ ⥤ Type u} (a₁ : F₁ ⟶ G₁) (a₂ : F₂ ⟶ G₂)
    (ha₁ : relativeAlgebraicSpaces P a₁) (ha₂ : relativeAlgebraicSpaces P a₂) :
    relativeAlgebraicSpaces P (prod.map a₁ a₂) := sorry

end AlgebraicGeometry.AlgebraicSpace
