module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.RestrictionTopos
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sheafification.Types
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

open AlgebraicGeometry.AlgebraicSpace

/- 66.18.11.1: if `f : X ⟶ Y` is étale, restriction of a sheaf of sets along
`etaleRestriction f` equals inverse image along the topos morphism associated to that
functor, i.e. `𝒢|_{X_étale} = f_small⁻¹ 𝒢`. -/
@[stacks 03LQ] #check
  (AlgebraicGeometry.AlgebraicSpace.smallEtaleMorphismOfTopoi_etaleRestrictionSheaf :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f],
      (smallEtaleMorphismOfTopoi f).inverseImage ≅ etaleRestrictionSheaf f (Type (u + 1)))

