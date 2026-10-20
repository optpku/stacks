/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.QuasiFinite
import StacksCheckRecall

/-!
# Étale morphisms of algebraic spaces are locally quasi-finite
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.39.5: An étale morphism of algebraic spaces is locally quasi-finite. -/
@[stacks 03XU] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_of_etale :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y), [AlgebraicGeometry.AlgebraicSpace.Etale f] →
        AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite f)
