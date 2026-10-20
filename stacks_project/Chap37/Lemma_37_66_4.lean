/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.IndQuasiAffine.Comparison
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.66.4 (1): Any quasi-affine morphism is ind-quasi-affine. -/
@[stacks 0F1W] #check
  (AlgebraicGeometry.QuasiAffineHom.indQuasiAffineHom :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y},
      AlgebraicGeometry.QuasiAffineHom f → AlgebraicGeometry.IndQuasiAffineHom f)

/- Lemma 37.66.4 (2): Any immersion is ind-quasi-affine. -/
@[stacks 0F1W] #check
  (AlgebraicGeometry.IsImmersion.indQuasiAffineHom :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y},
      AlgebraicGeometry.IsImmersion f → AlgebraicGeometry.IndQuasiAffineHom f)
