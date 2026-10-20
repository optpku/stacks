/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Affine.Spec
public import ReasLib.AlgebraicGeometry.FormalDeformation.Restriction
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.TwoAffineOpenCover

/-!
# Restriction of algebra deformations along a two-chart affine overlap

Each leg of the restriction cospan takes spectrum, restricts to the corresponding
infinitesimal overlap open, and takes its global sections.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {X : Scheme.{u}}

/-- The open of `Spec Γ(X, U₁)` corresponding to `U₁ ⊓ U₂`. -/
abbrev overlapOpenSpec₁ (c : TwoAffineOpenCover X) : (Spec Γ(X, c.U₁)).Opens :=
  c.fromSpec₁ ⁻¹ᵁ (c.U₁ ⊓ c.U₂)

/-- The open of `Spec Γ(X, U₂)` corresponding to `U₁ ⊓ U₂`. -/
abbrev overlapOpenSpec₂ (c : TwoAffineOpenCover X) : (Spec Γ(X, c.U₂)).Opens :=
  c.fromSpec₂ ⁻¹ᵁ (c.U₁ ⊓ c.U₂)

/-- `fromSpec₁` is an open immersion. -/
theorem isOpenImmersion_fromSpec₁ (c : TwoAffineOpenCover X) :
    IsOpenImmersion c.fromSpec₁ :=
  inferInstanceAs (IsOpenImmersion c.isAffine_U₁.fromSpec)

/-- `fromSpec₂` is an open immersion. -/
theorem isOpenImmersion_fromSpec₂ (c : TwoAffineOpenCover X) :
    IsOpenImmersion c.fromSpec₂ :=
  inferInstanceAs (IsOpenImmersion c.isAffine_U₂.fromSpec)

/-- The composite open immersion of the first overlap open into `X`. -/
theorem isOpenImmersion_overlapOpenSpec₁_ι_fromSpec (c : TwoAffineOpenCover X) :
    IsOpenImmersion ((overlapOpenSpec₁ c).ι ≫ c.fromSpec₁) :=
  @IsOpenImmersion.comp _ _ _ (overlapOpenSpec₁ c).ι c.fromSpec₁
    inferInstance (isOpenImmersion_fromSpec₁ c)

/-- The composite open immersion of the second overlap open into `X`. -/
theorem isOpenImmersion_overlapOpenSpec₂_ι_fromSpec (c : TwoAffineOpenCover X) :
    IsOpenImmersion ((overlapOpenSpec₂ c).ι ≫ c.fromSpec₂) :=
  @IsOpenImmersion.comp _ _ _ (overlapOpenSpec₂ c).ι c.fromSpec₂
    inferInstance (isOpenImmersion_fromSpec₂ c)

/-- The overlap open of `Spec Γ(X, U₁)` is isomorphic to `U₁ ⊓ U₂` over `X`. -/
def overlapIso₁ (c : TwoAffineOpenCover X) :
    (overlapOpenSpec₁ c).toScheme ≅ (c.U₁ ⊓ c.U₂).toScheme :=
  @IsOpenImmersion.isoOfRangeEq _ _ _
    ((overlapOpenSpec₁ c).ι ≫ c.fromSpec₁) (c.U₁ ⊓ c.U₂).ι
    (isOpenImmersion_overlapOpenSpec₁_ι_fromSpec c) inferInstance <| by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    exact congr_arg (SetLike.coe : X.Opens → Set X)
      ((c.isAffine_U₁.fromSpec.image_preimage_eq_opensRange_inf (c.U₁ ⊓ c.U₂)).trans
        (by simp [IsAffineOpen.opensRange_fromSpec]))

/-- The overlap open of `Spec Γ(X, U₂)` is isomorphic to `U₁ ⊓ U₂` over `X`. -/
def overlapIso₂ (c : TwoAffineOpenCover X) :
    (overlapOpenSpec₂ c).toScheme ≅ (c.U₁ ⊓ c.U₂).toScheme :=
  @IsOpenImmersion.isoOfRangeEq _ _ _
    ((overlapOpenSpec₂ c).ι ≫ c.fromSpec₂) (c.U₁ ⊓ c.U₂).ι
    (isOpenImmersion_overlapOpenSpec₂_ι_fromSpec c) inferInstance <| by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    exact congr_arg (SetLike.coe : X.Opens → Set X)
      ((c.isAffine_U₂.fromSpec.image_preimage_eq_opensRange_inf (c.U₁ ⊓ c.U₂)).trans
        (by simp [IsAffineOpen.opensRange_fromSpec]))

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (c : TwoAffineOpenCover X)
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))

/-- The structure morphism of `Spec P₁` over `k`. -/
def specStructureHom₁ :
    Spec (CommRingCat.of (hX.sectionsAlgOverSpec c.U₁)) ⟶
      Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier) :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₁
  FlatSchemeCat.specStructureHom Λ k P

/-- The structure morphism of `Spec P₂` over `k`. -/
def specStructureHom₂ :
    Spec (CommRingCat.of (hX.sectionsAlgOverSpec c.U₂)) ⟶
      Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier) :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₂
  FlatSchemeCat.specStructureHom Λ k P

/-- The deformation category of `Spec P₁`. -/
abbrev deformationCategory_spec₁ :=
  FlatSchemeCat.deformationCategory Λ k (Spec (CommRingCat.of (hX.sectionsAlgOverSpec c.U₁)))
    (specStructureHom₁ Λ k c hX)

/-- The deformation category of `Spec P₂`. -/
abbrev deformationCategory_spec₂ :=
  FlatSchemeCat.deformationCategory Λ k (Spec (CommRingCat.of (hX.sectionsAlgOverSpec c.U₂)))
    (specStructureHom₂ Λ k c hX)

/-- The deformation category of the first overlap open of `Spec P₁`. -/
abbrev deformationCategory_overlap₁ :=
  FlatSchemeCat.deformationCategory Λ k (overlapOpenSpec₁ c).toScheme
    ((overlapOpenSpec₁ c).ι ≫ specStructureHom₁ Λ k c hX)

/-- The deformation category of the second overlap open of `Spec P₂`. -/
abbrev deformationCategory_overlap₂ :=
  FlatSchemeCat.deformationCategory Λ k (overlapOpenSpec₂ c).toScheme
    ((overlapOpenSpec₂ c).ι ≫ specStructureHom₂ Λ k c hX)

/-- The ordinary functor `Def_{P₁} ⥤ Def_{Spec P₁}`. -/
def specFunctor₁ : deformationCategory_ring₁ Λ k c hX ⥤ deformationCategory_spec₁ Λ k c hX :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₁
  FlatSchemeCat.specFunctor Λ k P

/-- The ordinary functor `Def_{P₂} ⥤ Def_{Spec P₂}`. -/
def specFunctor₂ : deformationCategory_ring₂ Λ k c hX ⥤ deformationCategory_spec₂ Λ k c hX :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₂
  FlatSchemeCat.specFunctor Λ k P

/-- The `A`-algebra of global sections of a deformation of `overlapOpenSpec₁`. -/
def overlapSectionsObj₁ (Y : deformationCategory_overlap₁ Λ k c hX) : FlatAlgebraCat Λ k :=
  FlatAlgebraCat.of Y.left.base (Γ(Y.left.scheme, ⊤) : Type u)
    (isAlgebra := Scheme.Hom.globalSectionsAlgebra Y.left.structureHom)
    (isFlat := by sorry)

/-- The ring map `Γ(W, ⊤) →+* P₁₂` of a deformation of the first overlap open. -/
def overlapSectionsRingHom₁ (Y : deformationCategory_overlap₁ Λ k c hX) :
    Γ(Y.left.scheme, ⊤) →+* Γ(X, c.U₁ ⊓ c.U₂) :=
  (Y.hom.schemeHom.appTop ≫ (overlapIso₁ c).inv.appTop ≫ (c.U₁ ⊓ c.U₂).topIso.hom).hom

/-- The residue object `(k, P₁₂)`. -/
abbrev ofResidue_ringInf : FlatAlgebraCat Λ k :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec (c.U₁ ⊓ c.U₂)
  FlatAlgebraCat.ofResidue Λ k P

/-- The slice projection of `Def_{P₁}` to `C_Λ`. -/
abbrev algebraForget_ring₁ : deformationCategory_ring₁ Λ k c hX ⥤ ArtinianLocalAlgCat Λ k :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₁
  FlatSchemeCat.algebraDeformationForget Λ k P

/-- The slice projection of `Def_{P₂}` to `C_Λ`. -/
abbrev algebraForget_ring₂ : deformationCategory_ring₂ Λ k c hX ⥤ ArtinianLocalAlgCat Λ k :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₂
  FlatSchemeCat.algebraDeformationForget Λ k P

/-- The slice projection of `Def_{P₁₂}` to `C_Λ`. -/
abbrev algebraForget_ringInf : deformationCategory_ringInf Λ k c hX ⥤ ArtinianLocalAlgCat Λ k :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec (c.U₁ ⊓ c.U₂)
  FlatSchemeCat.algebraDeformationForget Λ k P

/-- The morphism `(A, Γ(W, ⊤)) ⟶ (k, P₁₂)` induced by a deformation of `overlapOpenSpec₁`. -/
def overlapSectionsResidueHom₁ (Y : deformationCategory_overlap₁ Λ k c hX) :
    overlapSectionsObj₁ Λ k c hX Y ⟶ ofResidue_ringInf Λ k c hX := by
  let Q := overlapSectionsObj₁ Λ k c hX Y
  let P := ofResidue_ringInf Λ k c hX
  let base : Q.base ⟶ P.base := Y.hom.baseHom
  let ring : Q.algebra →+* P.algebra := overlapSectionsRingHom₁ Λ k c hX Y
  have certificates :
      (ring.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp base.hom.toRingHom) ∧
      (∀ commutes, Function.Bijective (FlatAlgebraCat.canonicalTensorMap base ring commutes)) :=
    sorry
  exact FlatAlgebraCat.Hom.of base ring certificates.1 (certificates.2 certificates.1)

/-- A morphism of deformations of `overlapOpenSpec₁` induces the map on global sections. -/
def overlapSectionsMap₁ {src tgt : deformationCategory_overlap₁ Λ k c hX} (f : src ⟶ tgt) :
    overlapSectionsObj₁ Λ k c hX src ⟶ overlapSectionsObj₁ Λ k c hX tgt := by
  let Q := overlapSectionsObj₁ Λ k c hX src
  let P := overlapSectionsObj₁ Λ k c hX tgt
  let base : Q.base ⟶ P.base := f.left.baseHom
  let ring : Q.algebra →+* P.algebra := f.left.schemeHom.appTop.hom
  have certificates :
      (ring.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp base.hom.toRingHom) ∧
      (∀ commutes, Function.Bijective (FlatAlgebraCat.canonicalTensorMap base ring commutes)) :=
    sorry
  exact FlatAlgebraCat.Hom.of base ring certificates.1 (certificates.2 certificates.1)

/-- The functor `Def_{overlapOpenSpec₁} ⥤ Def_{P₁₂}` sending `(A, W)` to `(A, Γ(W, ⊤))`. -/
def overlapSectionsFunctor₁ :
    deformationCategory_overlap₁ Λ k c hX ⥤ deformationCategory_ringInf Λ k c hX := by
  have certificates :
      (∀ {src tgt : deformationCategory_overlap₁ Λ k c hX} (f : src ⟶ tgt),
        overlapSectionsMap₁ Λ k c hX f ≫ overlapSectionsResidueHom₁ Λ k c hX tgt =
          overlapSectionsResidueHom₁ Λ k c hX src) ∧
      (∀ Y : deformationCategory_overlap₁ Λ k c hX,
        overlapSectionsMap₁ Λ k c hX (𝟙 Y) = 𝟙 (overlapSectionsObj₁ Λ k c hX Y)) ∧
      (∀ {src mid tgt : deformationCategory_overlap₁ Λ k c hX}
        (f : src ⟶ mid) (g : mid ⟶ tgt),
        overlapSectionsMap₁ Λ k c hX (f ≫ g) =
          overlapSectionsMap₁ Λ k c hX f ≫ overlapSectionsMap₁ Λ k c hX g) := sorry
  exact {
    obj := fun Y ↦ Over.mk (overlapSectionsResidueHom₁ Λ k c hX Y)
    map := fun f ↦ Over.homMk (overlapSectionsMap₁ Λ k c hX f) (certificates.1 f)
    map_id := fun Y ↦ by apply Over.OverMorphism.ext; exact certificates.2.1 Y
    map_comp := fun f g ↦ by apply Over.OverMorphism.ext; exact certificates.2.2 f g }

/-- The ordinary functor `Def_{P₁} ⥤ Def_{P₁₂}` of restriction along `U₁₂ ⊂ U₁`. -/
def restrictRingFunctor₁ :
    deformationCategory_ring₁ Λ k c hX ⥤ deformationCategory_ringInf Λ k c hX :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₁
  (specFunctor₁ Λ k c hX).comp
    ((@FlatSchemeCat.restrictFunctor Λ k _ _ _ _ _ (Spec (CommRingCat.of P))
        (specStructureHom₁ Λ k c hX) (FlatSchemeCat.instFlat_specStructureHom Λ k P)
        (overlapOpenSpec₁ c)).comp
      (overlapSectionsFunctor₁ Λ k c hX))

/-- `restrictRingFunctor₁` lies strictly over `ArtinianLocalAlgCat`. -/
theorem restrictRingFunctor₁_comp_forget :
    (restrictRingFunctor₁ Λ k c hX).comp (algebraForget_ringInf Λ k c hX) =
      algebraForget_ring₁ Λ k c hX :=
  sorry

/-- The morphism `Def_{P₁} ⥤ᵇ Def_{P₁₂}` of categories over `ArtinianLocalAlgCat`. -/
def restrictRing₁ :
    BasedCategory.ofFunctor (algebraForget_ring₁ Λ k c hX) ⥤ᵇ
      BasedCategory.ofFunctor (algebraForget_ringInf Λ k c hX) :=
  BasedFunctor.ofFunctor (restrictRingFunctor₁ Λ k c hX)
    (restrictRingFunctor₁_comp_forget Λ k c hX)

/-- The underlying ordinary functor of `restrictRing₁` is `restrictRingFunctor₁`. -/
theorem restrictRing₁_toFunctor :
    (restrictRing₁ Λ k c hX).toFunctor = restrictRingFunctor₁ Λ k c hX :=
  rfl

/-- `restrictRing₁` commutes strictly with the projections to `ArtinianLocalAlgCat`. -/
theorem restrictRing₁_comp_forget :
    (restrictRing₁ Λ k c hX).toFunctor.comp (algebraForget_ringInf Λ k c hX) =
      algebraForget_ring₁ Λ k c hX :=
  (restrictRing₁ Λ k c hX).w

/-- The `A`-algebra of global sections of a deformation of `overlapOpenSpec₂`. -/
def overlapSectionsObj₂ (Y : deformationCategory_overlap₂ Λ k c hX) : FlatAlgebraCat Λ k :=
  FlatAlgebraCat.of Y.left.base (Γ(Y.left.scheme, ⊤) : Type u)
    (isAlgebra := Scheme.Hom.globalSectionsAlgebra Y.left.structureHom)
    (isFlat := by sorry)

/-- The ring map `Γ(W, ⊤) →+* P₁₂` of a deformation of the second overlap open. -/
def overlapSectionsRingHom₂ (Y : deformationCategory_overlap₂ Λ k c hX) :
    Γ(Y.left.scheme, ⊤) →+* Γ(X, c.U₁ ⊓ c.U₂) :=
  (Y.hom.schemeHom.appTop ≫ (overlapIso₂ c).inv.appTop ≫ (c.U₁ ⊓ c.U₂).topIso.hom).hom

/-- The morphism `(A, Γ(W, ⊤)) ⟶ (k, P₁₂)` induced by a deformation of `overlapOpenSpec₂`. -/
def overlapSectionsResidueHom₂ (Y : deformationCategory_overlap₂ Λ k c hX) :
    overlapSectionsObj₂ Λ k c hX Y ⟶ ofResidue_ringInf Λ k c hX := by
  let Q := overlapSectionsObj₂ Λ k c hX Y
  let P := ofResidue_ringInf Λ k c hX
  let base : Q.base ⟶ P.base := Y.hom.baseHom
  let ring : Q.algebra →+* P.algebra := overlapSectionsRingHom₂ Λ k c hX Y
  have certificates :
      (ring.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp base.hom.toRingHom) ∧
      (∀ commutes, Function.Bijective (FlatAlgebraCat.canonicalTensorMap base ring commutes)) :=
    sorry
  exact FlatAlgebraCat.Hom.of base ring certificates.1 (certificates.2 certificates.1)

/-- A morphism of deformations of `overlapOpenSpec₂` induces the map on global sections. -/
def overlapSectionsMap₂ {src tgt : deformationCategory_overlap₂ Λ k c hX} (f : src ⟶ tgt) :
    overlapSectionsObj₂ Λ k c hX src ⟶ overlapSectionsObj₂ Λ k c hX tgt := by
  let Q := overlapSectionsObj₂ Λ k c hX src
  let P := overlapSectionsObj₂ Λ k c hX tgt
  let base : Q.base ⟶ P.base := f.left.baseHom
  let ring : Q.algebra →+* P.algebra := f.left.schemeHom.appTop.hom
  have certificates :
      (ring.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp base.hom.toRingHom) ∧
      (∀ commutes, Function.Bijective (FlatAlgebraCat.canonicalTensorMap base ring commutes)) :=
    sorry
  exact FlatAlgebraCat.Hom.of base ring certificates.1 (certificates.2 certificates.1)

/-- The functor `Def_{overlapOpenSpec₂} ⥤ Def_{P₁₂}` sending `(A, W)` to `(A, Γ(W, ⊤))`. -/
def overlapSectionsFunctor₂ :
    deformationCategory_overlap₂ Λ k c hX ⥤ deformationCategory_ringInf Λ k c hX := by
  have certificates :
      (∀ {src tgt : deformationCategory_overlap₂ Λ k c hX} (f : src ⟶ tgt),
        overlapSectionsMap₂ Λ k c hX f ≫ overlapSectionsResidueHom₂ Λ k c hX tgt =
          overlapSectionsResidueHom₂ Λ k c hX src) ∧
      (∀ Y : deformationCategory_overlap₂ Λ k c hX,
        overlapSectionsMap₂ Λ k c hX (𝟙 Y) = 𝟙 (overlapSectionsObj₂ Λ k c hX Y)) ∧
      (∀ {src mid tgt : deformationCategory_overlap₂ Λ k c hX}
        (f : src ⟶ mid) (g : mid ⟶ tgt),
        overlapSectionsMap₂ Λ k c hX (f ≫ g) =
          overlapSectionsMap₂ Λ k c hX f ≫ overlapSectionsMap₂ Λ k c hX g) := sorry
  exact {
    obj := fun Y ↦ Over.mk (overlapSectionsResidueHom₂ Λ k c hX Y)
    map := fun f ↦ Over.homMk (overlapSectionsMap₂ Λ k c hX f) (certificates.1 f)
    map_id := fun Y ↦ by apply Over.OverMorphism.ext; exact certificates.2.1 Y
    map_comp := fun f g ↦ by apply Over.OverMorphism.ext; exact certificates.2.2 f g }

/-- The ordinary functor `Def_{P₂} ⥤ Def_{P₁₂}` of restriction along `U₁₂ ⊂ U₂`. -/
def restrictRingFunctor₂ :
    deformationCategory_ring₂ Λ k c hX ⥤ deformationCategory_ringInf Λ k c hX :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₂
  (specFunctor₂ Λ k c hX).comp
    ((@FlatSchemeCat.restrictFunctor Λ k _ _ _ _ _ (Spec (CommRingCat.of P))
        (specStructureHom₂ Λ k c hX) (FlatSchemeCat.instFlat_specStructureHom Λ k P)
        (overlapOpenSpec₂ c)).comp
      (overlapSectionsFunctor₂ Λ k c hX))

/-- `restrictRingFunctor₂` lies strictly over `ArtinianLocalAlgCat`. -/
theorem restrictRingFunctor₂_comp_forget :
    (restrictRingFunctor₂ Λ k c hX).comp (algebraForget_ringInf Λ k c hX) =
      algebraForget_ring₂ Λ k c hX :=
  sorry

/-- The morphism `Def_{P₂} ⥤ᵇ Def_{P₁₂}` of categories over `ArtinianLocalAlgCat`. -/
def restrictRing₂ :
    BasedCategory.ofFunctor (algebraForget_ring₂ Λ k c hX) ⥤ᵇ
      BasedCategory.ofFunctor (algebraForget_ringInf Λ k c hX) :=
  BasedFunctor.ofFunctor (restrictRingFunctor₂ Λ k c hX)
    (restrictRingFunctor₂_comp_forget Λ k c hX)

/-- The underlying ordinary functor of `restrictRing₂` is `restrictRingFunctor₂`. -/
theorem restrictRing₂_toFunctor :
    (restrictRing₂ Λ k c hX).toFunctor = restrictRingFunctor₂ Λ k c hX :=
  rfl

/-- `restrictRing₂` commutes strictly with the projections to `ArtinianLocalAlgCat`. -/
theorem restrictRing₂_comp_forget :
    (restrictRing₂ Λ k c hX).toFunctor.comp (algebraForget_ringInf Λ k c hX) =
      algebraForget_ring₂ Λ k c hX :=
  (restrictRing₂ Λ k c hX).w

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
