/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Functor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.Basic

/-!
# Effectiveness of formal objects of contraction functors

For a contraction situation with separated source over the base, compatible
families on maximal-adic truncations are restrictions of values on the complete
local spectrum.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Over
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- If the source of a contraction situation is separated over the base, every
compatible family of values on the positive maximal-adic truncations of a
Noetherian complete local algebra with finite-type residue field is the
restriction of a value on its spectrum. -/
theorem hasEffectiveFormalObjects (σ : ContractionSituation S)
    [Separated (toBase σ.X')] (R : CompleteLocalSAlgebra S)
    (ξ : ∀ n, σ.functor.obj
      (op (asLocallyNoetherian (Over.mk (R.truncationToS n)))))
    (hξ : ∀ n,
      σ.functor.map (op (asLocallyNoetherianMap (R.stageHom n))) (ξ (n + 1)) =
        ξ n) :
    ∃ x : σ.functor.obj (op (asLocallyNoetherian (Over.mk R.toS))),
      ∀ n, σ.functor.map (op (asLocallyNoetherianMap (R.truncationOverHom n)))
          x = ξ n :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
