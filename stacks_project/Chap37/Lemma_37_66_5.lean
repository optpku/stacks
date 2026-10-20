/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.Cancellation
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.66.5: If a composite `f ≫ g` of scheme morphisms is ind-quasi-affine,
then `f` is ind-quasi-affine. -/
@[stacks 0F1X] #check
  (AlgebraicGeometry.IndQuasiAffineHom.of_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z},
      AlgebraicGeometry.IndQuasiAffineHom (f ≫ g) →
        AlgebraicGeometry.IndQuasiAffineHom f)
