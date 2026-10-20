module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Basic

/-!
# Étale descent for formal algebraic spaces

A sheaf satisfying the fixed-site presentation condition is a formal algebraic
space if it admits a jointly sheaf-surjective family of representable étale maps
from formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsFormalAlgebraicSpace

/-- A sheaf satisfying the fixed-site coequalizer presentation condition is a
formal algebraic space if it admits a jointly sheaf-surjective family of maps
from formal algebraic spaces, each representable by algebraic spaces and étale. -/
theorem ofEtaleCover {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsCoequalizerOfRepresentables X]
    {ι : Type (max u v)} {X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c)
    (hX : ∀ i, IsFormalAlgebraicSpace (X_ i)) (hπ : ∀ i, etale (π i))
    (h_surj : Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π)) :
    IsFormalAlgebraicSpace X := sorry

end IsFormalAlgebraicSpace
end AlgebraicGeometry
