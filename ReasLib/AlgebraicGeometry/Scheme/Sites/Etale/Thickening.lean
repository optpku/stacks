module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Thickening

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- For a thickening `i : S₀ ⟶ S`, base change induces an equivalence from schemes
étale over `S` to schemes étale over `S₀`. -/
instance smallEtalePullback_isEquivalence_of_isThickening
    {S₀ S : Scheme.{u}} (i : S₀ ⟶ S) [IsThickening i] :
    (smallEtalePullback i).IsEquivalence := sorry

end AlgebraicGeometry.Scheme
