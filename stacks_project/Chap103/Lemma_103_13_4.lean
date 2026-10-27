/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Affine
import StacksCheckRecall

/-!
# Quasi-coherent direct images along affine morphisms

Along an affine morphism of algebraic stacks, `f_{QCoh,*}` is exact and
preserves direct sums and all coefficient-universe-small colimits, while
`R^i f_{QCoh,*}` vanishes for every `i > 0`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y]

/- Lemma 103.13.4 (1): positive-degree quasi-coherent higher direct images vanish. -/
@[stacks 0GQY] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.higherDirectImage_isZero :
    ∀ (f : X ⟶ Y) [Groupoids.Hom.Affine f] (F : QCoh X) (i : ℕ),
      0 < i → IsZero ((QCoh.higherDirectImageFunctor f i).obj F))

/- Lemma 103.13.4 (2): quasi-coherent direct image is exact. -/
@[stacks 0GQY] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.directImage_exact :
    ∀ (f : X ⟶ Y) [Groupoids.Hom.Affine f],
      exactFunctor (QCoh X) (QCoh Y) (QCoh.directImage f))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.directImage_preservesFiniteLimits :
  ∀ (f : X ⟶ Y) [Groupoids.Hom.Affine f],
    PreservesFiniteLimits (QCoh.directImage f))

#check (AlgebraicGeometry.GroupoidsOver.QCoh.directImage_preservesFiniteColimits :
  ∀ (f : X ⟶ Y) [Groupoids.Hom.Affine f],
    PreservesFiniteColimits (QCoh.directImage f))

/- Lemma 103.13.4 (3): quasi-coherent direct image preserves direct sums. -/
@[stacks 0GQY] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.directImage_preservesCoproducts :
    ∀ (f : X ⟶ Y) [Groupoids.Hom.Affine f] (I : Type u),
      PreservesColimitsOfShape (Discrete I) (QCoh.directImage f))

/- Lemma 103.13.4 (4): quasi-coherent direct image preserves all small colimits. -/
@[stacks 0GQY] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.directImage_preservesColimits :
    ∀ (f : X ⟶ Y) [Groupoids.Hom.Affine f],
      PreservesColimitsOfSize.{u, u} (QCoh.directImage f))
