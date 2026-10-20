/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Ample
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.40.7: finite-type quasi-affine morphisms are quasi-projective through the shared API. -/
@[stacks 0B3H] #check
  (AlgebraicGeometry.QuasiAffineHom.quasiProjective_of_finiteType :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      [AlgebraicGeometry.Scheme.Hom.FiniteType f] →
        AlgebraicGeometry.QuasiAffineHom f → AlgebraicGeometry.QuasiProjective f)
