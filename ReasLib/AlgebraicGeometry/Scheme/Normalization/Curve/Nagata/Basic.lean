/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Skyscraper
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Curve.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Nagata
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Quotient
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Structure
public import ReasLib.RingTheory.Normalization.Basic

@[expose] public section

/-!
# Local normalization data of reduced Nagata curves

This leaf owns global normalization properties and the stalkwise and quotient
API for reduced Nagata curves.  Completion-specific facts live in the sibling
`Nagata/Completion` leaf.
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Normalization.Curve.Nagata

variable {X : Scheme.{u}} [IsReduced X] [Nagata X]

/-- The normalization morphism of a reduced Nagata curve is finite. -/
theorem finiteTo (hdim : topologicalKrullDim X = 1) :
    IsFinite X.normalizationTo := sorry

/-- The normalization morphism of a reduced Nagata curve is surjective. -/
theorem surjectiveTo (hdim : topologicalKrullDim X = 1) :
    Surjective X.normalizationTo := sorry

/-- The normalization morphism of a reduced Nagata curve is birational. -/
theorem birationalTo (hdim : topologicalKrullDim X = 1) :
    IsBirational X.normalizationTo := sorry

namespace Structure

/-- The normalization structure morphism of a reduced Nagata curve is monic. -/
theorem mapMono (hdim : topologicalKrullDim X = 1) :
    Mono (Normalization.Structure.map X) := sorry

/-- The normalization structure quotient is a coproduct of skyscraper modules at singular closed
points. -/
theorem quotientCoproductSkyscraper (hdim : topologicalKrullDim X = 1) :
    IsIsomorphic
      (Normalization.Structure.quotient X)
      (∐ fun x : {x : X // x ∈ closedPoints X ∧ ¬ IsRegularLocalRing (X.presheaf.stalk x)} ↦
        (RingedSpace.Module.Skyscraper.atPoint x.1
          (Normalization.Stalk.pushforwardQuotientModule X x.1) : X.Modules)) := sorry

end Structure

namespace Local

/-- The map from a source stalk to its normalization pushforward stalk is injective. -/
theorem mapInjective (x : X) :
    Function.Injective (Normalization.Stalk.pushforwardMap X x) := sorry

/-- The canonical map from a source stalk to its ring normalization is injective. -/
theorem normalizationMapInjective (x : X) :
    Function.Injective
      (algebraMap (X.presheaf.stalk x)
        (Normalization.normalizationRing (X.presheaf.stalk x))) := sorry

/-- The local ring at a closed point of a reduced Nagata curve has Krull dimension one
provided the point has a strict generization.

Global dimension one alone permits isolated zero-dimensional components. For example, the
closed point on the `Spec k` component of `Spec (k[t] × k)` has a field as its local ring.
The strict-generization hypothesis excludes this case without imposing purity on `X`.
This is a local helper; Stacks 0C1R does not state it separately. -/
theorem krullDimEqOne (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X)
    (hgenerization : ∃ y : X, y ≠ x ∧ y ⤳ x) :
    ringKrullDim (X.presheaf.stalk x) = 1 := sorry

/-- The normalization pushforward stalk at a closed point is equivalent to the canonical ring
normalization of the source stalk. -/
theorem existsEquivNormalization (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    ∃ e : Normalization.Stalk.pushforward X x ≃+*
        Normalization.normalizationRing (X.presheaf.stalk x),
      e.toRingHom.comp (Normalization.Stalk.pushforwardMap X x) =
        algebraMap (X.presheaf.stalk x)
          (Normalization.normalizationRing (X.presheaf.stalk x)) := sorry

/-- A normalization pushforward stalk at a closed point admits an embedding into the source
total quotient ring under which it is the integral closure of the source stalk. -/
theorem existsIsIntegralClosure (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    ∃ f : Normalization.Stalk.pushforward X x →+*
        Localization (nonZeroDivisors (X.presheaf.stalk x)),
      f.comp (Normalization.Stalk.pushforwardMap X x) =
          algebraMap (X.presheaf.stalk x)
            (Localization (nonZeroDivisors (X.presheaf.stalk x))) ∧
        let _ : Algebra (Normalization.Stalk.pushforward X x)
            (Localization (nonZeroDivisors (X.presheaf.stalk x))) := f.toAlgebra
        IsIntegralClosure (Normalization.Stalk.pushforward X x)
          (X.presheaf.stalk x)
          (Localization (nonZeroDivisors (X.presheaf.stalk x))) := sorry

namespace Quotient

/-- The normalization quotient has nonzero length exactly when the closed-point local ring is
not regular. -/
theorem lengthNonzeroIffNotRegular (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    Normalization.Stalk.pushforwardQuotientLength X x ≠ 0 ↔
      ¬ IsRegularLocalRing (X.presheaf.stalk x) := sorry

/-- The normalization quotient at a closed point has finite length. -/
theorem lengthLtTop (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    Normalization.Stalk.pushforwardQuotientLength X x < ⊤ := sorry

/-- The finite length of the normalization quotient is the local `δ`-invariant. -/
theorem lengthEqDeltaInvariant (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    Normalization.Stalk.pushforwardQuotientLength X x =
      Normalization.deltaInvariant (X.presheaf.stalk x) := sorry

end Quotient

/-- The normalization pushforward stalk at a closed point has finite maximal spectrum. -/
theorem finiteMaximalSpectrum (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    Finite (MaximalSpectrum (Normalization.Stalk.pushforward X x)) := sorry

/-- The normalization pushforward stalk at a closed point is a finite product of Dedekind
domains. -/
theorem existsFiniteProductDedekind (hdim : topologicalKrullDim X = 1)
    (x : X) (hx : x ∈ closedPoints X) :
    ∃ (ι : Type u) (_hι : Finite ι) (R : ι → Type u)
      (_hR : ∀ i, CommRing (R i))
      (e : Normalization.Stalk.pushforward X x ≃+* Π i, R i),
      ∀ i, IsDedekindDomain (R i) := sorry

end Local

end AlgebraicGeometry.Scheme.Normalization.Curve.Nagata
