module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.StrictTransform.OpenImmersion

/-!
# Domination by admissible blowups

This module records when a proper morphism is dominated by a blowup supported away from an
open subscheme.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A proper morphism that is an isomorphism over a quasi-compact open of a quasi-compact,
quasi-separated base is dominated by an admissible blowup away from that open. -/
theorem exists_isAdmissibleBlowup_dominating
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (f : X ⟶ S) [IsProper f]
    (U : S.Opens) [QuasiCompact U.ι] [IsIso (f ∣_ U)] :
    ∃ (S' : Scheme.{u}) (b : S' ⟶ S) (g : S' ⟶ X),
      IsAdmissibleBlowup U b ∧ g ≫ f = b := sorry

end AlgebraicGeometry
