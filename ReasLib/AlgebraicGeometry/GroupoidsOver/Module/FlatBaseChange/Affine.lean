/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Affine
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale.SmallSections
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Pushforward
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Affine direct images of modules with flat base change -/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.LQCohFbc

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Affine f]

/-- Direct image along an affine morphism of algebraic stacks preserves finite
limits on locally quasi-coherent modules with flat base change. -/
instance directImage_preservesFiniteLimits : PreservesFiniteLimits (directImage f) :=
  sorry

/-- Direct image along an affine morphism of algebraic stacks preserves finite
colimits on locally quasi-coherent modules with flat base change. -/
instance directImage_preservesFiniteColimits :
    PreservesFiniteColimits (directImage f) :=
  sorry

/-- Direct image along an affine morphism of algebraic stacks is exact on
locally quasi-coherent modules with flat base change. -/
theorem directImage_exact : exactFunctor (LQCohFbc X) (LQCohFbc Y) (directImage f) :=
  (exactFunctor_iff (directImage f)).mpr
    ⟨directImage_preservesFiniteLimits f, directImage_preservesFiniteColimits f⟩

/-- Direct image along an affine morphism of algebraic stacks preserves direct
sums of locally quasi-coherent modules with flat base change. -/
instance directImage_preservesCoproducts (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (directImage f) :=
  sorry

/-- Every positive-degree higher direct image along an affine morphism of
algebraic stacks vanishes on locally quasi-coherent modules with flat base change. -/
theorem higherDirectImage_isZero (F : LQCohFbc X) (i : ℕ) (hi : 0 < i) :
    IsZero ((higherDirectImageFunctor f i).obj F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.LQCohFbc
