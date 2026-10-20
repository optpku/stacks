/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

/- Lemma 35.7.5: a quasi-coherent scheme module whose pullbacks along an fpqc covering
family are flat is itself flat. -/
@[stacks 05B1] #check
  (AlgebraicGeometry.Scheme.Modules.IsFlat.of_fpqcCovering :
    ∀ {X : Scheme.{u}} {ι : Type v}
      (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      (family : ι → Over X), Scheme.FpqcCovering family →
      (∀ i : ι, ((Scheme.Modules.pullback (family i).hom).obj ℱ).IsFlat) →
      ℱ.IsFlat)
