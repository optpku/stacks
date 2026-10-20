/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.ConormalBaseChange
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Ramification
public import ReasLib.RingTheory.Smooth.AtPrime.Fiber
public import ReasLib.RingTheory.Smooth.DVRFactorization

/-!
# A smoothness criterion at the closed center of a DVR factorization

The reusable core is phrased using the Kähler module after base change to the
target DVR.  A source-facing companion consumes the conormal cokernel of any
surjective smooth presentation.
-/

@[expose] public section

noncomputable section

open Ideal IsLocalRing
open scoped TensorProduct

universe u v w x

namespace Algebra.DVR.Factorization.ClosedCenter

variable {R : Type u} {L : Type v}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
variable [Algebra R L] [IsExtensionOfDiscreteValuationRings R L]
variable [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]

/-- Lemma 16.4.4 (tag 0BJ5), canonical form: smoothness at the generic center together with
freeness of `L ⊗[ A ] Ω[A/R]` implies smoothness at the closed center. -/
@[stacks 0BJ5]
theorem smooth_of_kaehler
    (S : Algebra.DVR.Factorization R L)
    (hgeneric : Algebra.SmoothAtPrime R S.mid S.genericPoint)
    [hfree : Module.Free L (L ⊗[S.mid] Ω[S.mid⁄R])] :
    Algebra.SmoothAtPrime R S.mid S.closedPoint := sorry

/-- Lemma 16.4.4 (tag 0BJ5), presentation form: if `B → A` is a surjective presentation,
`B` is smooth at the induced closed center, `A` is smooth at the generic center, and the
base-changed conormal cokernel is free over `L`, then `A` is smooth at the closed center. -/
@[stacks 0BJ5]
theorem smooth_of_presentation
    (S : Algebra.DVR.Factorization R L)
    (P : S.toTarget.SurjectivePresentation)
    (hpresentation : Algebra.SmoothAtPrime R P.B P.closedCenterPoint)
    (hgeneric : Algebra.SmoothAtPrime R S.mid S.genericPoint)
    [hfree : Module.Free L P.ConormalCokernel] :
    Algebra.SmoothAtPrime R S.mid S.closedPoint := sorry

end Algebra.DVR.Factorization.ClosedCenter
