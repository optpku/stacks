/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Ample
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 29.37.6: A morphism of schemes is quasi-affine if and only if its structure sheaf is
relatively ample. -/
@[stacks 0891] #check
  (AlgebraicGeometry.quasiAffineHom_iff_structureSheaf_relativelyAmple :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S),
      QuasiAffineHom f ↔ RelativelyAmple f (SheafOfModules.unit X.ringCatSheaf))
