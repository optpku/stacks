module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Standard

/-!
# Instances for chosen big standard sites

This module exposes the canonical pullback and subcanonical structures used by representable
descent independently of the numbered source-facing lemma.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u v

/-- A chosen big site uses its specified pullbacks as the canonical pullbacks on its carrier. -/
instance chosenBigSiteHasPullbacks {P : Precoverage Scheme.{u}}
    (𝒮 : ChosenBigSite.{u, v} P) : Limits.HasPullbacks 𝒮.carrier := sorry

/-- The topology of a chosen big standard site is subcanonical. -/
instance chosenBigStandardSiteSubcanonical (τ : StandardTopology)
    (𝒮 : ChosenBigSite.{u, v} τ.precoverage) : 𝒮.toGrothendieck.Subcanonical := sorry
