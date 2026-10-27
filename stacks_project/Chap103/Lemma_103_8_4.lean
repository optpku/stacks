/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.Affine
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.FlatBaseChange.Affine
import StacksCheckRecall

/-!
# Affine direct images of locally quasi-coherent modules with flat base change

Along an affine morphism of algebraic stacks, `f_*` is exact on `LQCoh^{fbc}`
and preserves direct sums, while `R^i f_*` vanishes on `LQCoh^{fbc}` for every
`i > 0`.
-/

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver
open scoped Bicategory

universe u

/- Lemma 103.8.4: affine direct image is exact on locally quasi-coherent modules
with flat base change. -/
@[stacks 0GQI] #check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.directImage_exact :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Groupoids.Hom.Affine f],
    exactFunctor (LQCohFbc X) (LQCohFbc Y) (LQCohFbc.directImage f))

/- Lemma 103.8.4: affine direct image commutes with direct sums. -/
@[stacks 0GQI] #check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.directImage_preservesCoproducts :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Groupoids.Hom.Affine f] (I : Type u),
    PreservesColimitsOfShape (Discrete I) (LQCohFbc.directImage f))

/- Lemma 103.8.4: positive-degree higher direct images vanish. -/
@[stacks 0GQI] #check (AlgebraicGeometry.GroupoidsOver.LQCohFbc.higherDirectImage_isZero :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) [Groupoids.Hom.Affine f] (F : LQCohFbc X) (i : ℕ),
    0 < i → IsZero ((LQCohFbc.higherDirectImageFunctor f i).obj F))
