/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.LocallyProjective.Fpqc
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

/- Lemma 74.6.5: a quasi-coherent module `ℱ` on an algebraic space `X` over a
scheme `S` is locally projective if its pullbacks along an fpqc covering family
are locally projective. -/
@[stacks 060Y]
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsLocallyProjective.of_fpqcCovering :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (family : ι → Over X),
      AlgebraicSpace.FpqcCovering family →
      (∀ i, AlgebraicSpace.Modules.IsLocallyProjective
        ((AlgebraicSpace.Modules.pullback (family i).hom).obj ℱ)) →
      AlgebraicSpace.Modules.IsLocallyProjective ℱ)
