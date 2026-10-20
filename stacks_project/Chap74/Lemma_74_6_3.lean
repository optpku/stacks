/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Flat.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

/- Lemma 74.6.3: a quasi-coherent module `F` on an algebraic space `X` over a
scheme `S` is a flat `𝒪_X`-module if its pullbacks along an fpqc covering family
are flat. -/
@[stacks 060W] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IsFlat.of_fpqcCovering :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
      (F : X.Modules) [F.IsQuasicoherent]
      (family : ι → Over X), FpqcCovering family →
      (∀ i : ι, ((Modules.pullback (family i).hom).obj F).IsFlat) →
      F.IsFlat)
