/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.OpenImmersion
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.UpperShriek

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Compactification.Of

/-- The canonical upper-shriek model for an open immersion is naturally isomorphic to
bounded-below derived pullback. -/
noncomputable def upperShriekIsoPullback {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (j : X ⟶ Y)
    [h_j : IsOpenImmersion j.hom.left] :
    upperShriek j (openImmersion j) (𝟭 (DerivedQCoh.Plus Y.obj.left)) ≅
      @DerivedQCoh.OpenImmersion.pullbackPlus _ _ j.hom.left h_j :=
  Functor.leftUnitor
    (@DerivedQCoh.OpenImmersion.pullbackPlus _ _ j.hom.left h_j)

/-- The forward component of the open-immersion upper-shriek comparison is the identity. -/
theorem upperShriekIsoPullback_hom_app {S : Scheme.{u}} [IsNoetherian S]
    {X Y : Scheme.FiniteTypeSeparatedOver S} (j : X ⟶ Y)
    [IsOpenImmersion j.hom.left] (M : DerivedQCoh.Plus Y.obj.left) :
    (upperShriekIsoPullback j).hom.app M = 𝟙 _ := sorry

end AlgebraicGeometry.Scheme.Compactification.Of
