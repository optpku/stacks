/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Completion
public import ReasLib.RingTheory.Completion.LocalRing

@[expose] public section

/-!
# Completed normalization data of reduced Nagata curves

This leaf owns completion-specific consequences and comparison maps for
normalization of reduced Nagata curves.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Normalization.Curve.Nagata

variable {X : Scheme.{u}} [IsReduced X] [Nagata X]

namespace Completion

/-- The completion of the local ring at a closed point of a reduced Nagata curve is reduced. -/
theorem isReduced (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    _root_.IsReduced (Normalization.Stalk.completion X x) := sorry

/-- The completion of the local ring at a closed point of a reduced Nagata curve is Noetherian. -/
theorem isNoetherian (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    IsNoetherianRing (Normalization.Stalk.completion X x) := sorry

/-- The completion of the local ring at a closed point of a reduced Nagata curve is complete
local. -/
theorem isCompleteLocal (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    _root_.IsCompleteLocalRing (Normalization.Stalk.completion X x) := sorry

/-- The completion of the local ring at a closed point of a reduced Nagata curve has Krull
dimension one. -/
theorem krullDimEqOne (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    ringKrullDim (Normalization.Stalk.completion X x) = 1 := sorry

/-- Base change of the ring normalization to the completed source stalk agrees with the
normalization completion. -/
theorem existsTensorEquivNormalization (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    ∃ e : Normalization.Stalk.normalizationTensor X x ≃ₐ[Normalization.Stalk.completion X x]
        Normalization.Stalk.normalizationCompletion X x,
      e.toRingHom.comp
          (algebraMap (Normalization.Stalk.completion X x)
            (Normalization.Stalk.normalizationTensor X x)) =
        algebraMap (Normalization.Stalk.completion X x)
          (Normalization.Stalk.normalizationCompletion X x) := sorry

/-- The completion of a normalization pushforward stalk agrees with the canonical normalization
completion. -/
theorem existsPushforwardEquivNormalization (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    ∃ e : Normalization.Stalk.pushforwardCompletion X x ≃ₐ[Normalization.Stalk.completion X x]
        Normalization.Stalk.normalizationCompletion X x,
      e.toRingHom.comp (Normalization.Stalk.completionToPushforward X x) =
        Normalization.Stalk.completionToNormalization X x := sorry

/-- A completed normalization pushforward stalk admits an embedding into the completed source
total quotient ring under which it is the integral closure of the completed source stalk. -/
theorem existsIsIntegralClosure (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    ∃ f : Normalization.Stalk.pushforwardCompletion X x →+*
        Localization (nonZeroDivisors (Normalization.Stalk.completion X x)),
      f.comp (Normalization.Stalk.completionToPushforward X x) =
          algebraMap (Normalization.Stalk.completion X x)
            (Localization (nonZeroDivisors (Normalization.Stalk.completion X x))) ∧
        let _ : Algebra (Normalization.Stalk.pushforwardCompletion X x)
            (Localization (nonZeroDivisors (Normalization.Stalk.completion X x))) := f.toAlgebra
        IsIntegralClosure (Normalization.Stalk.pushforwardCompletion X x)
          (Normalization.Stalk.completion X x)
          (Localization (nonZeroDivisors (Normalization.Stalk.completion X x))) := sorry

/-- A completed normalization pushforward stalk at a closed point is a finite product of complete
discrete valuation rings. -/
theorem existsFiniteProductCompleteDVR (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    ∃ (ι : Type u) (_hι : Finite ι) (R : ι → Type u)
      (_hR : ∀ i, CommRing (R i)) (_hDomain : ∀ i, IsDomain (R i))
      (_hAlgebra : ∀ i, Algebra (Normalization.Stalk.completion X x) (R i))
      (_hDVR : ∀ i, IsDiscreteValuationRing (R i))
      (e : Normalization.Stalk.pushforwardCompletion X x ≃ₐ[Normalization.Stalk.completion X x]
        Π i, R i),
      ∀ i, _root_.IsCompleteLocalRing (R i) := sorry

/-- Completion induces an isomorphism from the local normalization quotient to the completed
normalization quotient. -/
theorem quotientIsomorphicTo (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    IsIsomorphic (Normalization.Stalk.pushforwardQuotientModule X x)
      (Normalization.Stalk.pushforwardCompletionQuotientModule X x) := sorry

end Completion

end AlgebraicGeometry.Scheme.Normalization.Curve.Nagata
