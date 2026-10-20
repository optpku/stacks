module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.RingedTopos.Representable

@[expose] public section
open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory
universe u

namespace AlgebraicGeometry.GroupoidsOver
variable {S : Scheme.{u}}
variable {𝒳 : GroupoidsOver S} {X : Over S} (e : 𝒳 ≌ slice X) (τ : StandardTopology)
variable [HasSheafify (associatedRingedSite 𝒳 τ).siteTopology (Type u)]
variable [HasSheafify (associatedRingedSite (slice X) τ).siteTopology (Type u)]
variable [∀ P : 𝒳.totalᵒᵖ ⥤ Type u, (toFunctor e.hom).op.HasPointwiseRightKanExtension P]
variable [∀ P : (associatedRingedSite (slice X) τ).carrierᵒᵖ ⥤ Type u,
    X.iteratedSliceForward.op.HasPointwiseRightKanExtension P]


#check (AlgebraicGeometry.GroupoidsOver.associatedRingedSiteToposHom e τ :
  RingedSite.ToposHom (associatedRingedSite 𝒳 τ)
    (StandardTopology.Big.ringedSite τ X.left))

end AlgebraicGeometry.GroupoidsOver
