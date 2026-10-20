module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Map

/-!
# Relative-spectrum morphisms over a scheme morphism

A map `A → f_*B` supplies ring maps into each inverse-image open of the concrete
spectrum of B. Applying the actual Γ–Spec map locally and gluing across the
pulled-back affine cover constructs the resulting scheme morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {S T : Scheme.{u}} {A : S.QcAlgebraUnder} {B : T.QcAlgebraUnder}

/-- Push forward an algebra's given structure map along the specified base morphism. -/
def qcAlgebraPushforwardTarget (f : T ⟶ S) (B : T.QcAlgebraUnder) :
    Under S.sheaf :=
  Under.mk
    (Hom.commRingSheafPushforwardMap f.toShHom ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.toShHom.hom.base).map B.obj.hom)

/-- The ring map on an affine base open, evaluated by B's constructed universal algebra map. -/
def relativeSpectrumMapOverAffineRingHom (f : T ⟶ S)
    (α : A.obj ⟶ qcAlgebraPushforwardTarget f B) (U : S.affineOpens) :
    qcAlgebraSectionRing A U ⟶
      (relativeSpectrumOver B).scheme.presheaf.obj
        (op (((relativeSpectrumOver B).π ≫ f) ⁻¹ᵁ (U : S.Opens))) :=
  (InducedCategory.Hom.hom α.right).app (op (U : S.Opens)) ≫
    (InducedCategory.Hom.hom (relativeSpectrumGluedUniversalAlgebraMap B).right).app
      (op (f ⁻¹ᵁ (U : S.Opens)))

/-- The local relative-spectrum map on one chart of the pulled-back affine base cover. -/
def relativeSpectrumMapOverAffine (f : T ⟶ S)
    (α : A.obj ⟶ qcAlgebraPushforwardTarget f B) (U : S.affineOpens) :
    pullback ((relativeSpectrumOver B).π ≫ f) (U : S.Opens).ι ⟶
      (relativeSpectrumOver A).scheme :=
  (pullbackRestrictIsoRestrict ((relativeSpectrumOver B).π ≫ f) (U : S.Opens)).hom ≫
    (((relativeSpectrumOver B).π ≫ f) ⁻¹ᵁ (U : S.Opens)).toSpecΓ ≫
      Spec.map (relativeSpectrumMapOverAffineRingHom f α U) ≫
        colimit.ι (relativeSpectrumNativeGluingData A).functor U

/-- Glue the actual local Γ–Spec maps into a spectrum morphism over the specified base map. -/
def relativeSpectrumMapOver (f : T ⟶ S)
    (α : A.obj ⟶ qcAlgebraPushforwardTarget f B) :
    (relativeSpectrumOver B).scheme ⟶ (relativeSpectrumOver A).scheme :=
  Scheme.OpenCover.glueMorphismsOfLocallyDirected
    ((S.directedAffineCover).pullback₁ ((relativeSpectrumOver B).π ≫ f))
    (fun (U : S.affineOpens) ↦ relativeSpectrumMapOverAffine f α U)
    sorry

/-- The constructed spectrum morphism has the structural composite specified by f. -/
theorem relativeSpectrumMapOver_toBase (f : T ⟶ S)
    (α : A.obj ⟶ qcAlgebraPushforwardTarget f B) :
    relativeSpectrumMapOver f α ≫ (relativeSpectrumOver A).π =
      (relativeSpectrumOver B).π ≫ f := sorry

/-- Restriction to the pulled-back affine cover computes by the specified local Γ–Spec map. -/
theorem relativeSpectrumMapOver_pullbackCover (f : T ⟶ S)
    (α : A.obj ⟶ qcAlgebraPushforwardTarget f B) (U : S.affineOpens) :
    pullback.fst ((relativeSpectrumOver B).π ≫ f) (U : S.Opens).ι ≫
        relativeSpectrumMapOver f α = relativeSpectrumMapOverAffine f α U := sorry

end AlgebraicGeometry.Scheme
