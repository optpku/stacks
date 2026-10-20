module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.system :
    ∀ {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}
      (f : X' ⟶ X) (i : Z ⟶ X),
      [IsLocallyNoetherian X] →
      [IsClosedImmersion i] →
      [Proper f] →
      IsIsoOverOpen f
        (closedImmersionComplementι i) →
      ℕ ⥤ AlgebraicSpace S)
