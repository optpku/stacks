/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Cohomology
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open CategoryTheory.Limits

universe u

/- Lemma 37.11.9: if `T` is affine, `F` and `G` are quasi-coherent `T`-modules,
and `F` is locally projective, then the first cohomology of `internalHom F G` vanishes. -/
@[stacks 0D0E] #check
  (AlgebraicGeometry.Scheme.Modules.IsLocallyProjective.internalHom_firstCohomology_isZero :
    ∀ {T : Scheme.{u}} [IsAffine T]
      (F G : T.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] [IsLocallyProjective F],
      IsZero (cohomology (internalHom F G) 1))
