/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FiniteLocallyFree.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

/- Lemma 74.6.4: a quasi-coherent module on an algebraic space whose pullbacks along an
fpqc covering family are finite locally free is itself finite locally free. -/
@[stacks 060X] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsFiniteLocallyFree.of_fpqcCovering :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (family : ι → Over X), AlgebraicSpace.FpqcCovering family →
      (∀ i : ι,
        ((AlgebraicSpace.Modules.pullback (family i).hom).obj ℱ).IsFiniteLocallyFree) →
      ℱ.IsFiniteLocallyFree)
