module

public import Mathlib.Data.List.TFAE
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap94.Lemma_94_14_3_Pullback
public import stacks_project.Chap101.Lemma_101_25_5_Flat
public import stacks_project.Chap101.Lemma_101_36_4_Etale
public import stacks_project.Chap101.Lemma_101_36_4_Unramified
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation

/-!
# Characterizations of étale morphisms of algebraic stacks

A morphism of algebraic stacks is étale if and only if it is locally of finite
presentation, flat, and unramified, equivalently if and only if it is locally
of finite presentation, flat, and its relative 2-diagonal is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Etale

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- Lemma 101.36.10: Let `f : X ⟶ Y` be a morphism of algebraic stacks. The
following are equivalent: `Etale f`; `LocallyOfFinitePresentation f`, `Flat f`,
and `Unramified f`; and `LocallyOfFinitePresentation f`, `Flat f`, and
`Etale (Hom.diagonal f)`.

Stacks writes the diagonal of `f` as `Δ : X ⟶ X ×_Y X`; the Lean morphism is
`Hom.diagonal f : X ⟶ TwoFibreProduct.apex f f`. -/
@[stacks 0CJ1]
theorem tfae (f : X ⟶ Y) :
    List.TFAE
      [Etale f,
        LocallyOfFinitePresentation f ∧ Flat f ∧ Unramified f,
        LocallyOfFinitePresentation f ∧
          Flat f ∧ Etale (Hom.diagonal.{u + 1, u, u + 1} f)] :=
  sorry

/-- A morphism of algebraic stacks is étale if and only if it is locally of
finite presentation, flat, and unramified. -/
@[stacks 0CJ1]
theorem iff_locallyOfFinitePresentation_flat_unramified (f : X ⟶ Y) :
    Etale f ↔ LocallyOfFinitePresentation f ∧ Flat f ∧ Unramified f :=
  sorry

/-- A morphism of algebraic stacks is étale if and only if it is locally of
finite presentation, flat, and its relative 2-diagonal is étale. -/
@[stacks 0CJ1]
theorem iff_locallyOfFinitePresentation_flat_etale_diagonal (f : X ⟶ Y) :
    Etale f ↔
      LocallyOfFinitePresentation f ∧
        Flat f ∧ Etale (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- An étale morphism of algebraic stacks is locally of finite presentation. -/
@[stacks 0CJ1]
instance locallyOfFinitePresentation (f : X ⟶ Y) [Etale f] :
    LocallyOfFinitePresentation f :=
  sorry

/-- An étale morphism of algebraic stacks is flat. -/
@[stacks 0CJ1]
instance flat (f : X ⟶ Y) [Etale f] :
    Flat f :=
  sorry

/-- A locally of finite presentation, flat, unramified morphism of algebraic
stacks is étale. -/
@[stacks 0CJ1, instance 900]
instance of_locallyOfFinitePresentation_of_flat_of_unramified (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat f] [Unramified f] :
    Etale f :=
  sorry

/-- A locally of finite presentation, flat morphism of algebraic stacks whose
relative 2-diagonal is étale is étale. -/
@[stacks 0CJ1, instance 900]
instance of_locallyOfFinitePresentation_of_flat_of_etale_diagonal (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [Flat f]
    [Etale (Hom.diagonal.{u + 1, u, u + 1} f)] :
    Etale f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Etale
