/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ProjectiveBundle
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 27.21.5: relative projective `n`-space over any scheme is a projective bundle for the
standard free module of rank `n + 1`. -/
@[stacks 01OE] #check
  (AlgebraicGeometry.ProjectiveSpace.toBase_hasProjectiveBundleRepresentation :
    ∀ (S : AlgebraicGeometry.Scheme.{u}) (n : ℕ),
      Nonempty
        (AlgebraicGeometry.Scheme.ProjectiveBundle.Representation
          (AlgebraicGeometry.ProjectiveSpace.toBase n S)
          (SheafOfModules.freeFin (n + 1))))
