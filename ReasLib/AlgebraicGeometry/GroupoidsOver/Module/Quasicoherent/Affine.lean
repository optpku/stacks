/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.HigherDirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Abelian
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Colimits
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.SmallSections

/-!
# Quasi-coherent direct images along affine morphisms

Along an affine morphism of algebraic stacks, quasi-coherent higher direct
images vanish in positive degrees, and quasi-coherent direct image is exact
and preserves coproducts and all coefficient-universe-small colimits.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Affine f]

/-- Quasi-coherent higher direct images along an affine morphism of algebraic
stacks vanish in every positive degree. -/
theorem higherDirectImage_isZero (F : QCoh X) (i : ℕ) (hi : 0 < i) :
    IsZero ((higherDirectImageFunctor f i).obj F) :=
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

/-- Quasi-coherent direct image along an affine morphism of algebraic stacks
is exact. -/
theorem directImage_exact : exactFunctor (QCoh X) (QCoh Y) (directImage f) := by
  exact (exactFunctor_iff (directImage f)).2 ⟨inferInstance, inferInstance⟩

/-- Quasi-coherent direct image along an affine morphism of algebraic stacks
preserves coproducts indexed in the coefficient universe. -/
instance directImage_preservesCoproducts (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (directImage f) :=
  sorry

/-- Quasi-coherent direct image along an affine morphism of algebraic stacks
preserves all colimits whose objects and morphisms lie in the coefficient universe. -/
instance directImage_preservesColimits :
    PreservesColimitsOfSize.{u, u} (directImage f) := by
  exact preservesColimits_of_preservesCoequalizers_and_coproducts (directImage f)

end AlgebraicGeometry.GroupoidsOver.QCoh
