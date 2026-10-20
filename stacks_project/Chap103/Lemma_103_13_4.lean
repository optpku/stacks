module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import stacks_project.Chap96.Lemma_96_15_1_Abelian
public import stacks_project.Chap101.Definition_101_9_1_Affine
public import stacks_project.Chap103.Lemma_103_8_4
public import stacks_project.Chap103.Proposition_103_11_1_DirectImage

/-!
# Quasi-coherent direct images along affine morphisms

Along an affine morphism of algebraic stacks, `f_{QCoh,*}` is exact and
preserves direct sums and all colimits, while `R^i f_{QCoh,*}` vanishes for
every `i > 0`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Affine f]

/-- Lemma 103.13.4 (1): if `f : X ⟶ Y` is an affine morphism of algebraic stacks,
then `R^i f_{QCoh,*}` vanishes for every `i > 0`. -/
@[stacks 0GQY]
theorem higherDirectImage_isZero (F : QCoh X) (i : ℕ) (hi : 0 < i) :
    IsZero ((higherDirectImageFunctor f i).obj F) :=
  sorry

/-- Lemma 103.13.4 (2): if `f : X ⟶ Y` is an affine morphism of algebraic stacks,
then `f_{QCoh,*} : QCoh X ⥤ QCoh Y` is an exact functor. -/
@[stacks 0GQY]
theorem directImage_exact : exactFunctor (QCoh X) (QCoh Y) (directImage f) :=
  sorry

/-- Quasi-coherent direct image along an affine morphism of algebraic stacks
preserves finite limits. -/
instance directImage_preservesFiniteLimits :
    PreservesFiniteLimits (directImage f) :=
  sorry

/-- Quasi-coherent direct image along an affine morphism of algebraic stacks
preserves finite colimits. -/
instance directImage_preservesFiniteColimits :
    PreservesFiniteColimits (directImage f) :=
  sorry

/-- Lemma 103.13.4 (3): if `f : X ⟶ Y` is an affine morphism of algebraic stacks,
then `f_{QCoh,*}` commutes with direct sums. -/
@[stacks 0GQY]
instance directImage_preservesCoproducts (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (directImage f) :=
  sorry

/-- Lemma 103.13.4 (4): if `f : X ⟶ Y` is an affine morphism of algebraic stacks,
then `f_{QCoh,*}` commutes with all colimits. -/
@[stacks 0GQY]
instance directImage_preservesColimits : PreservesColimits (directImage f) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
