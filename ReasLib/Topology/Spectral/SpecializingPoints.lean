/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Spectral.CompactOpenIntersection

/-!
# Spectral spaces of points specializing to a constructible subset

The generic difference cone for a directed compact-open intersection lives in
`ReasLib.Topology.CompactOpen.Difference`. This module owns the specialization
`W = nhdsKer E` and its spectral consequences.
-/

@[expose] public section

universe u

open CategoryTheory Set TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 5.24.8 (1): if `X` is spectral and `E` is constructible, then the points specializing
to `E` but outside `E` form a spectral subspace. -/
@[stacks 0AP0 "spectrality of the difference"]
theorem spectralSpace_specializingPoints_sdiff_constructible
    [SpectralSpace X] (E : Set X) (hE : IsConstructible E) :
    SpectralSpace (nhdsKer E \ E : Set X) := sorry

/-- Lemma 5.24.8 (2): the generic compact-open difference cone, specialized to `nhdsKer E`,
gives the source-form inverse-limit presentation of `nhdsKer E \ E`. -/
@[stacks 0AP0 "inverse-limit presentation of the difference"]
theorem specializingPointsSdiff_limitProperty
    (E : Set X) {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection (nhdsKer E) S) :
    ∀ (Y : TopCat.{u}) (f : ∀ U : S, Y ⟶ TopCat.of ((U.1 : Set X) \ E : Set X)),
      (∀ (U V : S) (hUV : U ≤ V),
        f U ≫ compactOpenSdiffInclusion E hUV = f V) →
        ∃! l : Y ⟶ TopCat.of (nhdsKer E \ E : Set X),
          ∀ U : S, l ≫ h.sdiffConeApp E U = f U := sorry
