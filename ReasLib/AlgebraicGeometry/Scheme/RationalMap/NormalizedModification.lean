/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RationalMap.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedDomination

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PartialMap

/-- An `S`-rational map from a two-dimensional Noetherian Nagata scheme to a proper
`S`-scheme extends over a finite sequence of normalized blowups at closed points,
beginning with the normalization of its source. -/
theorem exists_normalizedBlowupSequence_lift
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsNoetherian X] [Scheme.Nagata X] [IsProper (Y ↘ S)]
    (f : X.PartialMap Y) [f.IsOver S] (h_dim : topologicalKrullDim X = 2) :
    ∃ (Z : Scheme.{u}) (s : Scheme.NormalizedBlowupSequence X.normalization Z)
      (g : Z ⟶ Y),
      g ≫ (Y ↘ S) = (s.toSource ≫ X.normalizationTo) ≫ (X ↘ S) ∧
        ((s.toSource ≫ X.normalizationTo) ⁻¹ᵁ f.domain).ι ≫ g =
          ((s.toSource ≫ X.normalizationTo) ∣_ f.domain) ≫ f.hom := sorry

end AlgebraicGeometry.Scheme.PartialMap
