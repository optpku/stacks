/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Curve.Nagata

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

universe u

/-!
# Lemma 33.41.2 Canonical Recall

The reusable reduced-Nagata-curve API is organized by global structure,
local stalks, quotient modules, and completions.  This file preserves the
source label and ordering without retaining source-specific aliases.
-/

/- Lemma 33.41.2 (1): normalization of a reduced Nagata curve is finite. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.finiteTo :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1), IsFinite X.normalizationTo)

/- Lemma 33.41.2 (2): normalization of a reduced Nagata curve is surjective. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.surjectiveTo :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1), Surjective X.normalizationTo)

/- Lemma 33.41.2 (3): normalization of a reduced Nagata curve is birational. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.birationalTo :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1), IsBirational X.normalizationTo)

/- Lemma 33.41.2 (4): the normalization structure morphism is monic. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Structure.mapMono :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1), Mono (Scheme.Normalization.Structure.map X))

/- Lemma 33.41.2 (5): the normalization structure quotient is a coproduct of skyscraper
modules at singular closed points. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Structure.quotientCoproductSkyscraper :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1),
      IsIsomorphic
        (Scheme.Normalization.Structure.quotient X)
        (∐ fun x : {x : X // x ∈ closedPoints X ∧
            ¬ IsRegularLocalRing (X.presheaf.stalk x)} ↦
          (RingedSpace.Module.Skyscraper.atPoint x.1
            (Scheme.Normalization.Stalk.pushforwardQuotientModule X x.1) : X.Modules)))

/- Lemma 33.41.2 (6): a closed normalization pushforward stalk is an integral closure. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Local.existsIsIntegralClosure :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∈ closedPoints X),
      ∃ f : Scheme.Normalization.Stalk.pushforward X x →+*
          Localization (nonZeroDivisors (X.presheaf.stalk x)),
        f.comp (Scheme.Normalization.Stalk.pushforwardMap X x) =
            algebraMap (X.presheaf.stalk x)
              (Localization (nonZeroDivisors (X.presheaf.stalk x))) ∧
          let _ : Algebra (Scheme.Normalization.Stalk.pushforward X x)
              (Localization (nonZeroDivisors (X.presheaf.stalk x))) := f.toAlgebra
          IsIntegralClosure (Scheme.Normalization.Stalk.pushforward X x)
            (X.presheaf.stalk x)
            (Localization (nonZeroDivisors (X.presheaf.stalk x))))

/- Lemma 33.41.2 (7): the local normalization quotient has finite length. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Local.Quotient.lengthLtTop :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∈ closedPoints X),
      Scheme.Normalization.Stalk.pushforwardQuotientLength X x < ⊤)

/- Lemma 33.41.2 (8): the local normalization quotient length is the `δ`-invariant. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Local.Quotient.lengthEqDeltaInvariant :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∈ closedPoints X),
      Scheme.Normalization.Stalk.pushforwardQuotientLength X x =
        Normalization.deltaInvariant (X.presheaf.stalk x))

/- Lemma 33.41.2 (9): a closed normalization pushforward stalk is semilocal. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Local.finiteMaximalSpectrum :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∈ closedPoints X),
      Finite (MaximalSpectrum (Scheme.Normalization.Stalk.pushforward X x)))

/- Lemma 33.41.2 (10): a closed normalization pushforward stalk is a finite product of
Dedekind domains. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Local.existsFiniteProductDedekind :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∈ closedPoints X),
      ∃ (ι : Type u) (_hι : Finite ι) (R : ι → Type u)
        (_hR : ∀ i, CommRing (R i))
        (e : Scheme.Normalization.Stalk.pushforward X x ≃+* Π i, R i),
        ∀ i, IsDedekindDomain (R i))

/- Lemma 33.41.2 (11): a closed local-ring completion is reduced. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Completion.isReduced :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∈ closedPoints X),
      _root_.IsReduced (Scheme.Normalization.Stalk.completion X x))

/- Lemma 33.41.2 (12): a closed local-ring completion is Noetherian. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Completion.isNoetherian :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∈ closedPoints X),
      IsNoetherianRing (Scheme.Normalization.Stalk.completion X x))

/- Lemma 33.41.2 (13): a closed local-ring completion is complete local. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Completion.isCompleteLocal :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∈ closedPoints X),
      _root_.IsCompleteLocalRing (Scheme.Normalization.Stalk.completion X x))

/- Lemma 33.41.2 (14): a closed local-ring completion has Krull dimension one. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Completion.krullDimEqOne :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∈ closedPoints X),
      ringKrullDim (Scheme.Normalization.Stalk.completion X x) = 1)

/- Lemma 33.41.2 (15): a completed normalization pushforward stalk is an integral closure. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Completion.existsIsIntegralClosure :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∈ closedPoints X),
      ∃ f : Scheme.Normalization.Stalk.pushforwardCompletion X x →+*
          Localization (nonZeroDivisors (Scheme.Normalization.Stalk.completion X x)),
        f.comp (Scheme.Normalization.Stalk.completionToPushforward X x) =
            algebraMap (Scheme.Normalization.Stalk.completion X x)
              (Localization (nonZeroDivisors (Scheme.Normalization.Stalk.completion X x))) ∧
          let _ : Algebra (Scheme.Normalization.Stalk.pushforwardCompletion X x)
              (Localization (nonZeroDivisors (Scheme.Normalization.Stalk.completion X x))) :=
            f.toAlgebra
          IsIntegralClosure (Scheme.Normalization.Stalk.pushforwardCompletion X x)
            (Scheme.Normalization.Stalk.completion X x)
            (Localization (nonZeroDivisors (Scheme.Normalization.Stalk.completion X x))))

/- Lemma 33.41.2 (16): a completed normalization pushforward stalk is a finite product of
complete discrete valuation rings. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Completion.existsFiniteProductCompleteDVR :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∈ closedPoints X),
      ∃ (ι : Type u) (_hι : Finite ι) (R : ι → Type u)
        (_hR : ∀ i, CommRing (R i)) (_hDomain : ∀ i, IsDomain (R i))
        (_hAlgebra : ∀ i, Algebra (Scheme.Normalization.Stalk.completion X x) (R i))
        (_hDVR : ∀ i, IsDiscreteValuationRing (R i))
        (e : Scheme.Normalization.Stalk.pushforwardCompletion X x
          ≃ₐ[Scheme.Normalization.Stalk.completion X x] Π i, R i),
        ∀ i, _root_.IsCompleteLocalRing (R i))

/- Lemma 33.41.2 (17): the local normalization quotient agrees with its completed quotient. -/
@[stacks 0C1R] #check
  (AlgebraicGeometry.Scheme.Normalization.Curve.Nagata.Completion.quotientIsomorphicTo :
    ∀ {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [Scheme.Nagata X]
      (hdim : topologicalKrullDim X = 1) (x : X) (hx : x ∈ closedPoints X),
      IsIsomorphic (Scheme.Normalization.Stalk.pushforwardQuotientModule X x)
        (Scheme.Normalization.Stalk.pushforwardCompletionQuotientModule X x))
