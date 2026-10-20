/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Operations
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.13.4: quasi-affineness is stable under composition. -/
@[stacks 01SN] #check (AlgebraicGeometry.QuasiAffineHom.comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z},
    AlgebraicGeometry.QuasiAffineHom f → AlgebraicGeometry.QuasiAffineHom g →
      AlgebraicGeometry.QuasiAffineHom (f ≫ g))
