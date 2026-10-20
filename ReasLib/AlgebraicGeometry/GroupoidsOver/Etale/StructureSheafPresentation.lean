module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed

/-!
# Global-sections presentation of the associated étale structure sheaf

The structure sheaf of a groupoid fibration's associated étale site is identified
with the global-sections sheaf of its scheme realization.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The topology of `etaleRingedSite X` is the associated étale topology of `X`. -/
theorem etaleRingedSite_siteTopology (X : GroupoidsOver S) :
    (etaleRingedSite X).siteTopology = X.etaleTopology :=
  rfl

/-- The global-sections presheaf on `X_étale` is a sheaf. -/
theorem etaleRingedSite_structurePresheaf_isSheaf (X : GroupoidsOver S) :
    Presheaf.IsSheaf X.etaleTopology
      (Scheme.Site.structurePresheaf (X.p ⋙ Over.forget S)) :=
  sorry

/-- Identification of `O_X` with the global-sections sheaf of the realization
`X.p ⋙ Over.forget S`, via the identity on the common underlying presheaf. -/
def structureSheafPresentationIso (X : GroupoidsOver S) :
    (etaleRingedSite X).structureSheaf ≅
      ⟨Scheme.Site.structurePresheaf (X.p ⋙ Over.forget S),
        etaleRingedSite_structurePresheaf_isSheaf X⟩ where
  hom := Sheaf.homEquiv.symm (𝟙 _)
  inv := Sheaf.homEquiv.symm (𝟙 _)
  hom_inv_id := by
    apply Sheaf.hom_ext
    exact Category.id_comp _
  inv_hom_id := by
    apply Sheaf.hom_ext
    exact Category.id_comp _

/-- The forward map of `structureSheafPresentationIso` is the identity on the
underlying presheaf. -/
theorem structureSheafPresentationIso_hom (X : GroupoidsOver S) :
    (structureSheafPresentationIso X).hom = Sheaf.homEquiv.symm (𝟙 _) :=
  rfl

/-- The inverse map of `structureSheafPresentationIso` is the identity on the
underlying presheaf. -/
theorem structureSheafPresentationIso_inv (X : GroupoidsOver S) :
    (structureSheafPresentationIso X).inv = Sheaf.homEquiv.symm (𝟙 _) :=
  rfl

end AlgebraicGeometry.GroupoidsOver
