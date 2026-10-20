/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import stacks_project.Chap101.Definition_101_9_1_Affine
public import stacks_project.Chap103.Proposition_103_11_1_DirectImage

/-!
# Affine direct images of locally quasi-coherent modules with flat base change

Along an affine morphism of algebraic stacks, `f_*` is exact on `LQCoh^{fbc}`
and preserves direct sums, while `R^i f_*` vanishes on `LQCoh^{fbc}` for every
`i > 0`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace QuasiCompact

/-- An affine morphism of algebraic stacks is quasi-compact. -/
instance of_affine {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Affine f] : QuasiCompact f :=
  sorry

end QuasiCompact

namespace QuasiSeparated

/-- An affine morphism of algebraic stacks is quasi-separated. -/
instance of_affine {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.Affine f] : QuasiSeparated f :=
  sorry

end QuasiSeparated

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.GroupoidsOver.LQCohFbc

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [Groupoids.Hom.Affine f]

/-- Lemma 103.8.4 (1): if `f : X ⟶ Y` is an affine morphism of algebraic stacks,
then `f_* : LQCohFbc X ⥤ LQCohFbc Y` is an exact functor. -/
@[stacks 0GQI]
theorem directImage_exact : exactFunctor (LQCohFbc X) (LQCohFbc Y) (directImage f) :=
  sorry

/-- Direct image along an affine morphism of algebraic stacks preserves finite
limits. -/
instance directImage_preservesFiniteLimits : PreservesFiniteLimits (directImage f) :=
  sorry

/-- Direct image along an affine morphism of algebraic stacks preserves finite
colimits. -/
instance directImage_preservesFiniteColimits :
    PreservesFiniteColimits (directImage f) :=
  sorry

/-- Lemma 103.8.4 (2): if `f : X ⟶ Y` is an affine morphism of algebraic stacks,
then `f_* : LQCohFbc X ⥤ LQCohFbc Y` commutes with direct sums. -/
@[stacks 0GQI]
instance directImage_preservesCoproducts (I : Type u) :
    PreservesColimitsOfShape (Discrete I) (directImage f) :=
  sorry

/-- Lemma 103.8.4 (3): if `f : X ⟶ Y` is an affine morphism of algebraic stacks,
then `R^i f_*` vanishes on `LQCohFbc X` for every `i > 0`. -/
@[stacks 0GQI]
theorem higherDirectImage_isZero (F : LQCohFbc X) (i : ℕ) (hi : 0 < i) :
    IsZero ((higherDirectImageFunctor f i).obj F) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.LQCohFbc
