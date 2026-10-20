module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.TwoAffineOpenCover.Restriction
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic

/-!
# Gluing deformation categories along two affine opens

Restriction and global sections give the canonical comparison with the two-fibre
product of coordinate-ring deformation categories.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X : Scheme.{u}} (c : TwoAffineOpenCover X)
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
/-- The two-fibre product of the coordinate-ring deformation categories over the overlap. -/
abbrev ringDeformationPullback :=
  BasedCategory.PseudoPullback (restrictRing₁ Λ k c hX) (restrictRing₂ Λ k c hX)

/-- The projection of the two-fibre product returns its stored Artinian base. -/
theorem ringDeformationPullback_p_obj
    (P : (ringDeformationPullback Λ k c hX).obj) :
    (ringDeformationPullback Λ k c hX).p.obj P =
      BasedCategory.PseudoPullback.baseObj P :=
  rfl

variable [AlgebraicGeometry.Flat hX]

/-- The slice projection of `Def_X` to `C_Λ`. -/
abbrev schemeForget : FlatSchemeCat.deformationCategory Λ k X hX ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
    FlatSchemeCat.forget Λ k

/-- Transport a deformation of `U₁` along `U₁ ≅ Spec P₁`. -/
def transportSpec₁ (ξ : deformationCategory_U₁ Λ k c hX) :
    FlatSchemeCat.deformationCategory Λ k (Spec (CommRingCat.of (ring₁ c)))
      (specStructureHom₁ Λ k c hX) :=
  Over.mk <|
    FlatSchemeCat.Hom.of ξ.hom.baseHom (c.isoSpec₁.inv ≫ ξ.hom.schemeHom) sorry

/-- Transport a deformation of `U₂` along `U₂ ≅ Spec P₂`. -/
def transportSpec₂ (ξ : deformationCategory_U₂ Λ k c hX) :
    FlatSchemeCat.deformationCategory Λ k (Spec (CommRingCat.of (ring₂ c)))
      (specStructureHom₂ Λ k c hX) :=
  Over.mk <|
    FlatSchemeCat.Hom.of ξ.hom.baseHom (c.isoSpec₂.inv ≫ ξ.hom.schemeHom) sorry

/-- The deformation of `P₁` obtained by restricting `ξ` to `U₁` and taking global sections. -/
def glueFstObj (ξ : FlatSchemeCat.deformationCategory Λ k X hX) : deformationCategory_ring₁ Λ k c hX :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₁
  (FlatSchemeCat.globalSectionsFunctor Λ k P).obj
    (transportSpec₁ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₁).obj ξ))

/-- The deformation of `P₂` obtained by restricting `ξ` to `U₂` and taking global sections. -/
def glueSndObj (ξ : FlatSchemeCat.deformationCategory Λ k X hX) : deformationCategory_ring₂ Λ k c hX :=
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₂
  (FlatSchemeCat.globalSectionsFunctor Λ k P).obj
    (transportSpec₂ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₂).obj ξ))

/-- `glueFstObj` keeps the Artinian base of the original deformation. -/
theorem glueFstObj_left_base (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (glueFstObj Λ k c hX ξ).left.base = ξ.left.base :=
  rfl

/-- `glueSndObj` keeps the Artinian base of the original deformation. -/
theorem glueSndObj_left_base (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (glueSndObj Λ k c hX ξ).left.base = ξ.left.base :=
  rfl

/-- A morphism of deformations of `X` induces the corresponding morphism of `P₁`-deformations. -/
def glueFstMap {ξ η : FlatSchemeCat.deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    glueFstObj Λ k c hX ξ ⟶ glueFstObj Λ k c hX η := by
  let src := transportSpec₁ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₁).obj ξ)
  let tgt := transportSpec₁ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₁).obj η)
  let base := φ.left.baseHom
  let map := (FlatSchemeCat.restrictMap Λ k X hX c.U₁ φ).schemeHom
  have certificates :
      IsPullback map tgt.left.structureHom src.left.structureHom (FlatSchemeCat.specMap base) ∧
      (∀ cartesian, FlatSchemeCat.Hom.of (src := src.left) (tgt := tgt.left) base map cartesian ≫
        tgt.hom = src.hom) := sorry
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₁
  exact (FlatSchemeCat.globalSectionsFunctor Λ k P).map
    (Over.homMk (FlatSchemeCat.Hom.of base map certificates.1) (certificates.2 certificates.1))

/-- A morphism of deformations of `X` induces the corresponding morphism of `P₂`-deformations. -/
def glueSndMap {ξ η : FlatSchemeCat.deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    glueSndObj Λ k c hX ξ ⟶ glueSndObj Λ k c hX η := by
  let src := transportSpec₂ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₂).obj ξ)
  let tgt := transportSpec₂ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₂).obj η)
  let base := φ.left.baseHom
  let map := (FlatSchemeCat.restrictMap Λ k X hX c.U₂ φ).schemeHom
  have certificates :
      IsPullback map tgt.left.structureHom src.left.structureHom (FlatSchemeCat.specMap base) ∧
      (∀ cartesian, FlatSchemeCat.Hom.of (src := src.left) (tgt := tgt.left) base map cartesian ≫
        tgt.hom = src.hom) := sorry
  let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₂
  exact (FlatSchemeCat.globalSectionsFunctor Λ k P).map
    (Over.homMk (FlatSchemeCat.Hom.of base map certificates.1) (certificates.2 certificates.1))

/-- The first fibre component of the image of a deformation of `X`. -/
def glueFstFiber (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (algebraForget_ring₁ Λ k c hX).Fiber ξ.left.base :=
  Fiber.mk (a := glueFstObj Λ k c hX ξ) (glueFstObj_left_base Λ k c hX ξ)

/-- The second fibre component of the image of a deformation of `X`. -/
def glueSndFiber (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (algebraForget_ring₂ Λ k c hX).Fiber ξ.left.base :=
  Fiber.mk (a := glueSndObj Λ k c hX ξ) (glueSndObj_left_base Λ k c hX ξ)

/-- The corresponding open of `U₁` on a deformation of `X`. -/
abbrev correspondingOpen_U₁ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) : ξ.left.scheme.Opens :=
  ξ.hom.correspondingOpen c.U₁

/-- The corresponding open of `U₂` on a deformation of `X`. -/
abbrev correspondingOpen_U₂ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) : ξ.left.scheme.Opens :=
  ξ.hom.correspondingOpen c.U₂

/-- The corresponding open of `U₁ ⊓ U₂` on a deformation of `X`. -/
abbrev correspondingOpen_inf (ξ : FlatSchemeCat.deformationCategory Λ k X hX) : ξ.left.scheme.Opens :=
  ξ.hom.correspondingOpen (c.U₁ ⊓ c.U₂)

/-- The overlap open of a deformation of `X` is contained in the first chart open. -/
theorem correspondingOpen_inf_le_U₁ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    correspondingOpen_inf Λ k c hX ξ ≤ correspondingOpen_U₁ Λ k c hX ξ :=
  by
  exact Set.image_mono (SetLike.coe_mono (inf_le_left : c.U₁ ⊓ c.U₂ ≤ c.U₁))

/-- The overlap open of a deformation of `X` is contained in the second chart open. -/
theorem correspondingOpen_inf_le_U₂ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    correspondingOpen_inf Λ k c hX ξ ≤ correspondingOpen_U₂ Λ k c hX ξ :=
  by
  exact Set.image_mono (SetLike.coe_mono (inf_le_right : c.U₁ ⊓ c.U₂ ≤ c.U₂))

/-- Infinitesimal thickenings of affine opens remain affine. -/
theorem isAffine_correspondingOpen_U₁ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    IsAffine (correspondingOpen_U₁ Λ k c hX ξ).toScheme :=
  sorry

/-- Infinitesimal thickenings of affine opens remain affine. -/
theorem isAffine_correspondingOpen_U₂ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    IsAffine (correspondingOpen_U₂ Λ k c hX ξ).toScheme :=
  sorry

/-- The open of `Spec Γ(U₁_Y, ⊤)` corresponding to the affine overlap. -/
def glueFstOverlapOpen (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (Spec (CommRingCat.of (glueFstObj Λ k c hX ξ).left.algebra)).Opens :=
  ((specFunctor₁ Λ k c hX).obj (glueFstObj Λ k c hX ξ)).hom.correspondingOpen
    (overlapOpenSpec₁ c)

/-- The open of `Spec Γ(U₂_Y, ⊤)` corresponding to the affine overlap. -/
def glueSndOverlapOpen (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (Spec (CommRingCat.of (glueSndObj Λ k c hX ξ).left.algebra)).Opens :=
  ((specFunctor₂ Λ k c hX).obj (glueSndObj Λ k c hX ξ)).hom.correspondingOpen
    (overlapOpenSpec₂ c)

/-- Canonical map `Spec Γ(U₁_Y, ⊤) ⟶ Spec (Γ(U₁_Y, ⊤) : Type u)`. -/
private def specΓToSpecAlgebra₁ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    Spec Γ((correspondingOpen_U₁ Λ k c hX ξ).toScheme, ⊤) ⟶
      Spec (CommRingCat.of (glueFstObj Λ k c hX ξ).left.algebra) :=
  Spec.map (CommRingCat.ofHom (RingHom.id _))

/-- Canonical map `Spec Γ(U₂_Y, ⊤) ⟶ Spec (Γ(U₂_Y, ⊤) : Type u)`. -/
private def specΓToSpecAlgebra₂ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    Spec Γ((correspondingOpen_U₂ Λ k c hX ξ).toScheme, ⊤) ⟶
      Spec (CommRingCat.of (glueSndObj Λ k c hX ξ).left.algebra) :=
  Spec.map (CommRingCat.ofHom (RingHom.id _))

/-- `U₁₂_Y ⟶ Spec (Γ(U₁_Y, ⊤) : Type u)` is an open immersion. -/
theorem isOpenImmersion_overlapToSpecAlgebra₁ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    IsOpenImmersion
      (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₁ Λ k c hX ξ) ≫
        (correspondingOpen_U₁ Λ k c hX ξ).toScheme.toSpecΓ ≫
          specΓToSpecAlgebra₁ Λ k c hX ξ) :=
  sorry

/-- `U₁₂_Y ⟶ Spec (Γ(U₂_Y, ⊤) : Type u)` is an open immersion. -/
theorem isOpenImmersion_overlapToSpecAlgebra₂ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    IsOpenImmersion
      (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₂ Λ k c hX ξ) ≫
        (correspondingOpen_U₂ Λ k c hX ξ).toScheme.toSpecΓ ≫
          specΓToSpecAlgebra₂ Λ k c hX ξ) :=
  sorry

/-- Scheme isomorphism `U₁₂_Y ≅ W₁` of corresponding overlap opens. -/
def glueingOverlapIso₁ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (correspondingOpen_inf Λ k c hX ξ).toScheme ≅
      (glueFstOverlapOpen Λ k c hX ξ).toScheme :=
  @IsOpenImmersion.isoOfRangeEq _ _ _
    (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₁ Λ k c hX ξ) ≫
      (correspondingOpen_U₁ Λ k c hX ξ).toScheme.toSpecΓ ≫
        specΓToSpecAlgebra₁ Λ k c hX ξ)
    (glueFstOverlapOpen Λ k c hX ξ).ι
    (isOpenImmersion_overlapToSpecAlgebra₁ Λ k c hX ξ) inferInstance sorry

/-- Scheme isomorphism `U₁₂_Y ≅ W₂` of corresponding overlap opens. -/
def glueingOverlapIso₂ (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (correspondingOpen_inf Λ k c hX ξ).toScheme ≅
      (glueSndOverlapOpen Λ k c hX ξ).toScheme :=
  @IsOpenImmersion.isoOfRangeEq _ _ _
    (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₂ Λ k c hX ξ) ≫
      (correspondingOpen_U₂ Λ k c hX ξ).toScheme.toSpecΓ ≫
        specΓToSpecAlgebra₂ Λ k c hX ξ)
    (glueSndOverlapOpen Λ k c hX ξ).ι
    (isOpenImmersion_overlapToSpecAlgebra₂ Λ k c hX ξ) inferInstance sorry

/-- Scheme isomorphism of the two Spec-overlap opens of a deformation of `X`. -/
private def glueingOverlapSchemeIso (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (glueFstOverlapOpen Λ k c hX ξ).toScheme ≅
      (glueSndOverlapOpen Λ k c hX ξ).toScheme :=
  (glueingOverlapIso₁ Λ k c hX ξ).symm ≪≫ glueingOverlapIso₂ Λ k c hX ξ

/-- Global-sections ring map `Γ(W₁, ⊤) →+* Γ(W₂, ⊤)` of the overlap comparison. -/
private def glueingComparisonRingHom (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    Γ((glueFstOverlapOpen Λ k c hX ξ).toScheme, ⊤) →+*
      Γ((glueSndOverlapOpen Λ k c hX ξ).toScheme, ⊤) :=
  (glueingOverlapSchemeIso Λ k c hX ξ).inv.appTop.hom

/-- Inverse global-sections ring map `Γ(W₂, ⊤) →+* Γ(W₁, ⊤)` of the overlap comparison. -/
private def glueingComparisonRingHom_inv (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    Γ((glueSndOverlapOpen Λ k c hX ξ).toScheme, ⊤) →+*
      Γ((glueFstOverlapOpen Λ k c hX ξ).toScheme, ⊤) :=
  (glueingOverlapSchemeIso Λ k c hX ξ).hom.appTop.hom

/-- The first restricted ring deformation keeps the Artinian base of `ξ`. -/
theorem glueingComparison_fst_base (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueFstFiber Λ k c hX ξ)).1.left.base = ξ.left.base :=
  (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
    (glueFstFiber Λ k c hX ξ)).2

/-- The second restricted ring deformation keeps the Artinian base of `ξ`. -/
theorem glueingComparison_snd_base (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueSndFiber Λ k c hX ξ)).1.left.base = ξ.left.base :=
  (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
    (glueSndFiber Λ k c hX ξ)).2

/-- Forward morphism of restricted overlap algebras in `FlatAlgebraCat`. -/
def glueingComparisonAlgebraHom (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueFstFiber Λ k c hX ξ)).1.left ⟶
      (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueSndFiber Λ k c hX ξ)).1.left := by
  let Q := (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
    (glueFstFiber Λ k c hX ξ)).1.left
  let P := (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
    (glueSndFiber Λ k c hX ξ)).1.left
  let base : Q.base ⟶ P.base := eqToHom ((glueingComparison_fst_base Λ k c hX ξ).trans
    (glueingComparison_snd_base Λ k c hX ξ).symm)
  let ring : Q.algebra →+* P.algebra := glueingComparisonRingHom Λ k c hX ξ
  have certificates :
      (ring.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp base.hom.toRingHom) ∧
      (∀ commutes, Function.Bijective (FlatAlgebraCat.canonicalTensorMap base ring commutes)) :=
    sorry
  exact FlatAlgebraCat.Hom.of base ring certificates.1 (certificates.2 certificates.1)

/-- Inverse morphism of restricted overlap algebras in `FlatAlgebraCat`. -/
def glueingComparisonAlgebraInv (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueSndFiber Λ k c hX ξ)).1.left ⟶
      (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueFstFiber Λ k c hX ξ)).1.left := by
  let Q := (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
    (glueSndFiber Λ k c hX ξ)).1.left
  let P := (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
    (glueFstFiber Λ k c hX ξ)).1.left
  let base : Q.base ⟶ P.base := eqToHom ((glueingComparison_snd_base Λ k c hX ξ).trans
    (glueingComparison_fst_base Λ k c hX ξ).symm)
  let ring : Q.algebra →+* P.algebra := glueingComparisonRingHom_inv Λ k c hX ξ
  have certificates :
      (ring.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp base.hom.toRingHom) ∧
      (∀ commutes, Function.Bijective (FlatAlgebraCat.canonicalTensorMap base ring commutes)) :=
    sorry
  exact FlatAlgebraCat.Hom.of base ring certificates.1 (certificates.2 certificates.1)

/-- Ambient isomorphism of overlap algebras in `FlatAlgebraCat`. -/
def glueingComparisonAlgebraIso (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueFstFiber Λ k c hX ξ)).1.left ≅
      (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueSndFiber Λ k c hX ξ)).1.left := by
  let hom := glueingComparisonAlgebraHom Λ k c hX ξ
  let inv := glueingComparisonAlgebraInv Λ k c hX ξ
  have certificates : (hom ≫ inv = 𝟙 _) ∧ (inv ≫ hom = 𝟙 _) := sorry
  exact { hom := hom, inv := inv, hom_inv_id := certificates.1, inv_hom_id := certificates.2 }

/-- Comparison isomorphism in `Def_{P₁₂}` between the two restricted ring deformations. -/
def glueingComparisonIso (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    ((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj (glueFstFiber Λ k c hX ξ) ≅
      ((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj (glueSndFiber Λ k c hX ξ) := by
  let src := ((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj (glueFstFiber Λ k c hX ξ)
  let tgt := ((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj (glueSndFiber Λ k c hX ξ)
  let e := glueingComparisonAlgebraIso Λ k c hX ξ
  have certificates :
      (e.hom ≫ tgt.1.hom = src.1.hom) ∧
      (∀ compatible : e.hom ≫ tgt.1.hom = src.1.hom,
        (algebraForget_ringInf Λ k c hX).IsHomLift (𝟙 ξ.left.base)
          (Over.isoMk e compatible).hom) := sorry
  exact Functor.Fiber.isoMk (Over.isoMk e certificates.1) (certificates.2 certificates.1)

/-- The image of a deformation of `X` in the 2-fiber product of ring deformation categories. -/
def glueingObj (ξ : FlatSchemeCat.deformationCategory Λ k X hX) :
    (ringDeformationPullback Λ k c hX).obj :=
  BasedCategory.PseudoPullback.mk (restrictRing₁ Λ k c hX) (restrictRing₂ Λ k c hX) ξ.left.base
    { fst := glueFstFiber Λ k c hX ξ
      snd := glueSndFiber Λ k c hX ξ
      iso := glueingComparisonIso Λ k c hX ξ }

/-- A morphism of deformations of `X` induces a morphism of 2-fiber product objects. -/
def glueingMap {ξ η : FlatSchemeCat.deformationCategory Λ k X hX} (φ : ξ ⟶ η) :
    glueingObj Λ k c hX ξ ⟶ glueingObj Λ k c hX η := by
  let base := (schemeForget Λ k hX).map φ
  let fst := glueFstMap Λ k c hX φ
  let snd := glueSndMap Λ k c hX φ
  have certificates :
      (algebraForget_ring₁ Λ k c hX).IsHomLift base fst ∧
      (algebraForget_ring₂ Λ k c hX).IsHomLift base snd ∧
      CommSq ((restrictRing₁ Λ k c hX).toFunctor.map fst)
        (BasedCategory.PseudoPullback.comparison (glueingObj Λ k c hX ξ))
        (BasedCategory.PseudoPullback.comparison (glueingObj Λ k c hX η))
        ((restrictRing₂ Λ k c hX).toFunctor.map snd) := sorry
  exact BasedCategory.PseudoPullback.Hom.mk base fst certificates.1 snd
    certificates.2.1 certificates.2.2

/-- The ordinary functor `Def_X ⥤ Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`. -/
def glueingFunctor :
    FlatSchemeCat.deformationCategory Λ k X hX ⥤ (ringDeformationPullback Λ k c hX).obj := by
  have certificates :
      (∀ ξ : FlatSchemeCat.deformationCategory Λ k X hX,
        glueingMap Λ k c hX (𝟙 ξ) = 𝟙 (glueingObj Λ k c hX ξ)) ∧
      (∀ {ξ η ζ : FlatSchemeCat.deformationCategory Λ k X hX} (φ : ξ ⟶ η) (ψ : η ⟶ ζ),
        glueingMap Λ k c hX (φ ≫ ψ) = glueingMap Λ k c hX φ ≫ glueingMap Λ k c hX ψ) := sorry
  exact {
    obj := glueingObj Λ k c hX
    map := glueingMap Λ k c hX
    map_id := certificates.1
    map_comp := certificates.2 }

/-- `glueingFunctor` lies strictly over `ArtinianLocalAlgCat`. -/
theorem glueingFunctor_comp_forget :
    (glueingFunctor Λ k c hX).comp (ringDeformationPullback Λ k c hX).p =
      schemeForget Λ k hX :=
  sorry

/-- The based functor `Def_X ⥤ᵇ Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`. -/
def glueingBasedFunctor :
    BasedCategory.ofFunctor (schemeForget Λ k hX) ⥤ᵇ ringDeformationPullback Λ k c hX where
  toFunctor := glueingFunctor Λ k c hX
  w := glueingFunctor_comp_forget Λ k c hX

/-- The underlying ordinary functor of `glueingBasedFunctor` is `glueingFunctor`. -/
theorem glueingBasedFunctor_toFunctor :
    (glueingBasedFunctor Λ k c hX).toFunctor = glueingFunctor Λ k c hX :=
  rfl

/-- Restriction to a two-chart affine cover and global sections induce an equivalence
of deformation categories over the Artinian local algebra base. -/
theorem glueingBasedFunctor_isEquivalence :
    BasedFunctor.IsEquivalence (glueingBasedFunctor Λ k c hX) :=
  sorry

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
