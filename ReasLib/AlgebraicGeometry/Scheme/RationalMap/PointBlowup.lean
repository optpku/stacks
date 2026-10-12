/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RationalMap.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.PointDomination

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.PartialMap

/-- A partial map from a Noetherian regular two-dimensional scheme to a proper scheme over a
common base extends to a morphism over that base after a finite sequence of closed-point blowups
whose centers lie over the complement of the partial map's domain. -/
theorem exists_pointBlowupSequence_lift
    {S X Y : Scheme.{u}} [X.Over S] [Y.Over S]
    [IsNoetherian X] [Scheme.Regular X] [IsProper (Y ↘ S)]
    (f : X.PartialMap Y) [f.IsOver S] (h_dim : topologicalKrullDim X = 2) :
    ∃ (Xn : Scheme.{u}) (s : Scheme.PointBlowupSequence X Xn) (g : Xn ⟶ Y),
      s.EveryCenterOver (f.domain : Set X)ᶜ ∧
        (g ≫ (Y ↘ S) = s.toSource ≫ (X ↘ S) ∧
          (s.toSource ⁻¹ᵁ f.domain).ι ≫ g =
            (s.toSource ∣_ f.domain) ≫ f.hom) := sorry

end AlgebraicGeometry.Scheme.PartialMap
