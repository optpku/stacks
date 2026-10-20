/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.FiberIsoClasses
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 99.11.2: the relative Picard functor is the fppf sheafification of the
presheaf of isomorphism classes in the Picard fibres. -/
@[stacks 0D26] #check
  (AlgebraicGeometry.AlgebraicSpace.picardFunctor_sheafify_fiberIsoClasses :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X B : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ B), CategoryTheory.IsIso
        ((CategoryTheory.presheafToSheaf
          (AlgebraicGeometry.AlgebraicSpace.SchemesOver.fppfTopology B)
          (Type (u + 1))).map
            (AlgebraicGeometry.AlgebraicSpace.Picard.fiberIsoClassToPresheaf f)))
