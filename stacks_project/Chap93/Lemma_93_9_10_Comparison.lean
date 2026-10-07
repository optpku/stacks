module

public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic
public import stacks_project.Chap93.Lemma_93_9_10_Pullback

/-!
# Forward glueing functor of two-chart scheme deformations

Restriction to the two affine opens, followed by global sections, yields a
based functor `Def_X ⥤ᵇ Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`.
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
variable [AlgebraicGeometry.Flat hX]

/-- The slice projection of `Def_X` to `C_Λ`. -/
abbrev schemeForget : deformationCategory Λ k hX ⥤ ArtinianLocalAlgCat Λ k :=
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
def glueFstObj (ξ : deformationCategory Λ k hX) : deformationCategory_ring₁ Λ k c hX :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₁)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRing₁ Λ k c hX
  (FlatSchemeCat.globalSectionsFunctor Λ k (ring₁ c)).obj
    (transportSpec₁ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₁).obj ξ))

/-- The deformation of `P₂` obtained by restricting `ξ` to `U₂` and taking global sections. -/
def glueSndObj (ξ : deformationCategory Λ k hX) : deformationCategory_ring₂ Λ k c hX :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₂)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRing₂ Λ k c hX
  (FlatSchemeCat.globalSectionsFunctor Λ k (ring₂ c)).obj
    (transportSpec₂ Λ k c hX ((FlatSchemeCat.restrictFunctor Λ k X hX c.U₂).obj ξ))

/-- `glueFstObj` keeps the Artinian base of the original deformation. -/
theorem glueFstObj_left_base (ξ : deformationCategory Λ k hX) :
    (glueFstObj Λ k c hX ξ).left.base = ξ.left.base :=
  sorry

/-- `glueSndObj` keeps the Artinian base of the original deformation. -/
theorem glueSndObj_left_base (ξ : deformationCategory Λ k hX) :
    (glueSndObj Λ k c hX ξ).left.base = ξ.left.base :=
  sorry

/-- A morphism of deformations of `X` induces the corresponding morphism of `P₁`-deformations. -/
def glueFstMap {ξ η : deformationCategory Λ k hX} (φ : ξ ⟶ η) :
    glueFstObj Λ k c hX ξ ⟶ glueFstObj Λ k c hX η :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₁)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRing₁ Λ k c hX
  (FlatSchemeCat.globalSectionsFunctor Λ k (ring₁ c)).map
    (Over.homMk
      (FlatSchemeCat.Hom.of φ.left.baseHom
        ((FlatSchemeCat.restrictMap Λ k X hX c.U₁ φ).schemeHom) sorry)
      sorry)

/-- A morphism of deformations of `X` induces the corresponding morphism of `P₂`-deformations. -/
def glueSndMap {ξ η : deformationCategory Λ k hX} (φ : ξ ⟶ η) :
    glueSndObj Λ k c hX ξ ⟶ glueSndObj Λ k c hX η :=
  -- Local instance justification (noncanonical choice): the `k`-algebra structure on
  -- `Γ(X, U₂)` is induced by the structure morphism `hX` and cannot be a global instance.
  letI := algebraRing₂ Λ k c hX
  (FlatSchemeCat.globalSectionsFunctor Λ k (ring₂ c)).map
    (Over.homMk
      (FlatSchemeCat.Hom.of φ.left.baseHom
        ((FlatSchemeCat.restrictMap Λ k X hX c.U₂ φ).schemeHom) sorry)
      sorry)



/-- The first fibre component of the image of a deformation of `X`. -/
def glueFstFiber (ξ : deformationCategory Λ k hX) :
    (algebraForget_ring₁ Λ k c hX).Fiber ξ.left.base :=
  Fiber.mk (a := glueFstObj Λ k c hX ξ) (glueFstObj_left_base Λ k c hX ξ)

/-- The second fibre component of the image of a deformation of `X`. -/
def glueSndFiber (ξ : deformationCategory Λ k hX) :
    (algebraForget_ring₂ Λ k c hX).Fiber ξ.left.base :=
  Fiber.mk (a := glueSndObj Λ k c hX ξ) (glueSndObj_left_base Λ k c hX ξ)

/-- The corresponding open of `U₁` on a deformation of `X`. -/
abbrev correspondingOpen_U₁ (ξ : deformationCategory Λ k hX) : ξ.left.scheme.Opens :=
  ξ.hom.correspondingOpen c.U₁

/-- The corresponding open of `U₂` on a deformation of `X`. -/
abbrev correspondingOpen_U₂ (ξ : deformationCategory Λ k hX) : ξ.left.scheme.Opens :=
  ξ.hom.correspondingOpen c.U₂

/-- The corresponding open of `U₁ ⊓ U₂` on a deformation of `X`. -/
abbrev correspondingOpen_inf (ξ : deformationCategory Λ k hX) : ξ.left.scheme.Opens :=
  ξ.hom.correspondingOpen (c.U₁ ⊓ c.U₂)

/-- The overlap open of a deformation of `X` is contained in the first chart open. -/
theorem correspondingOpen_inf_le_U₁ (ξ : deformationCategory Λ k hX) :
    correspondingOpen_inf Λ k c hX ξ ≤ correspondingOpen_U₁ Λ k c hX ξ :=
  sorry

/-- The overlap open of a deformation of `X` is contained in the second chart open. -/
theorem correspondingOpen_inf_le_U₂ (ξ : deformationCategory Λ k hX) :
    correspondingOpen_inf Λ k c hX ξ ≤ correspondingOpen_U₂ Λ k c hX ξ :=
  sorry

/-- Infinitesimal thickenings of affine opens remain affine. -/
instance instIsAffine_correspondingOpen_U₁ (ξ : deformationCategory Λ k hX) :
    IsAffine (correspondingOpen_U₁ Λ k c hX ξ).toScheme :=
  sorry

/-- Infinitesimal thickenings of affine opens remain affine. -/
instance instIsAffine_correspondingOpen_U₂ (ξ : deformationCategory Λ k hX) :
    IsAffine (correspondingOpen_U₂ Λ k c hX ξ).toScheme :=
  sorry

/-- The open of `Spec Γ(U₁_Y, ⊤)` corresponding to the affine overlap. -/
def glueFstOverlapOpen (ξ : deformationCategory Λ k hX) :
    (Spec (CommRingCat.of (glueFstObj Λ k c hX ξ).left.algebra)).Opens :=
  ((specFunctor₁ Λ k c hX).obj (glueFstObj Λ k c hX ξ)).hom.correspondingOpen
    (overlapOpenSpec₁ c)

/-- The open of `Spec Γ(U₂_Y, ⊤)` corresponding to the affine overlap. -/
def glueSndOverlapOpen (ξ : deformationCategory Λ k hX) :
    (Spec (CommRingCat.of (glueSndObj Λ k c hX ξ).left.algebra)).Opens :=
  ((specFunctor₂ Λ k c hX).obj (glueSndObj Λ k c hX ξ)).hom.correspondingOpen
    (overlapOpenSpec₂ c)

/-- Canonical map `Spec Γ(U₁_Y, ⊤) ⟶ Spec (Γ(U₁_Y, ⊤) : Type u)`. -/
def specΓToSpecAlgebra₁ (ξ : deformationCategory Λ k hX) :
    Spec Γ((correspondingOpen_U₁ Λ k c hX ξ).toScheme, ⊤) ⟶
      Spec (CommRingCat.of (glueFstObj Λ k c hX ξ).left.algebra) :=
  Spec.map (CommRingCat.ofHom (RingHom.id _))

/-- Canonical map `Spec Γ(U₂_Y, ⊤) ⟶ Spec (Γ(U₂_Y, ⊤) : Type u)`. -/
def specΓToSpecAlgebra₂ (ξ : deformationCategory Λ k hX) :
    Spec Γ((correspondingOpen_U₂ Λ k c hX ξ).toScheme, ⊤) ⟶
      Spec (CommRingCat.of (glueSndObj Λ k c hX ξ).left.algebra) :=
  Spec.map (CommRingCat.ofHom (RingHom.id _))

/-- `U₁₂_Y ⟶ Spec (Γ(U₁_Y, ⊤) : Type u)` is an open immersion. -/
instance instIsOpenImmersion_overlapToSpecAlgebra₁ (ξ : deformationCategory Λ k hX) :
    IsOpenImmersion
      (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₁ Λ k c hX ξ) ≫
        (correspondingOpen_U₁ Λ k c hX ξ).toScheme.toSpecΓ ≫
          specΓToSpecAlgebra₁ Λ k c hX ξ) :=
  sorry

/-- `U₁₂_Y ⟶ Spec (Γ(U₂_Y, ⊤) : Type u)` is an open immersion. -/
instance instIsOpenImmersion_overlapToSpecAlgebra₂ (ξ : deformationCategory Λ k hX) :
    IsOpenImmersion
      (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₂ Λ k c hX ξ) ≫
        (correspondingOpen_U₂ Λ k c hX ξ).toScheme.toSpecΓ ≫
          specΓToSpecAlgebra₂ Λ k c hX ξ) :=
  sorry

/-- Scheme isomorphism `U₁₂_Y ≅ W₁` of corresponding overlap opens. -/
def glueingOverlapIso₁ (ξ : deformationCategory Λ k hX) :
    (correspondingOpen_inf Λ k c hX ξ).toScheme ≅
      (glueFstOverlapOpen Λ k c hX ξ).toScheme :=
  IsOpenImmersion.isoOfRangeEq
    (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₁ Λ k c hX ξ) ≫
      (correspondingOpen_U₁ Λ k c hX ξ).toScheme.toSpecΓ ≫
        specΓToSpecAlgebra₁ Λ k c hX ξ)
    (glueFstOverlapOpen Λ k c hX ξ).ι sorry

/-- Scheme isomorphism `U₁₂_Y ≅ W₂` of corresponding overlap opens. -/
def glueingOverlapIso₂ (ξ : deformationCategory Λ k hX) :
    (correspondingOpen_inf Λ k c hX ξ).toScheme ≅
      (glueSndOverlapOpen Λ k c hX ξ).toScheme :=
  IsOpenImmersion.isoOfRangeEq
    (ξ.left.scheme.homOfLE (correspondingOpen_inf_le_U₂ Λ k c hX ξ) ≫
      (correspondingOpen_U₂ Λ k c hX ξ).toScheme.toSpecΓ ≫
        specΓToSpecAlgebra₂ Λ k c hX ξ)
    (glueSndOverlapOpen Λ k c hX ξ).ι sorry

/-- Scheme isomorphism of the two Spec-overlap opens of a deformation of `X`. -/
def glueingOverlapSchemeIso (ξ : deformationCategory Λ k hX) :
    (glueFstOverlapOpen Λ k c hX ξ).toScheme ≅
      (glueSndOverlapOpen Λ k c hX ξ).toScheme :=
  (glueingOverlapIso₁ Λ k c hX ξ).symm ≪≫ glueingOverlapIso₂ Λ k c hX ξ

/-- Global-sections ring map `Γ(W₁, ⊤) →+* Γ(W₂, ⊤)` of the overlap comparison. -/
def glueingComparisonRingHom (ξ : deformationCategory Λ k hX) :
    Γ((glueFstOverlapOpen Λ k c hX ξ).toScheme, ⊤) →+*
      Γ((glueSndOverlapOpen Λ k c hX ξ).toScheme, ⊤) :=
  (glueingOverlapSchemeIso Λ k c hX ξ).inv.appTop.hom

/-- Inverse global-sections ring map `Γ(W₂, ⊤) →+* Γ(W₁, ⊤)` of the overlap comparison. -/
def glueingComparisonRingHom_inv (ξ : deformationCategory Λ k hX) :
    Γ((glueSndOverlapOpen Λ k c hX ξ).toScheme, ⊤) →+*
      Γ((glueFstOverlapOpen Λ k c hX ξ).toScheme, ⊤) :=
  (glueingOverlapSchemeIso Λ k c hX ξ).hom.appTop.hom

/-- The first restricted ring deformation keeps the Artinian base of `ξ`. -/
theorem glueingComparison_fst_base (ξ : deformationCategory Λ k hX) :
    (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueFstFiber Λ k c hX ξ)).1.left.base = ξ.left.base :=
  sorry

/-- The second restricted ring deformation keeps the Artinian base of `ξ`. -/
theorem glueingComparison_snd_base (ξ : deformationCategory Λ k hX) :
    (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueSndFiber Λ k c hX ξ)).1.left.base = ξ.left.base :=
  sorry

/-- Forward morphism of restricted overlap algebras in `FlatAlgebraCat`. -/
def glueingComparisonAlgebraHom (ξ : deformationCategory Λ k hX) :
    (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueFstFiber Λ k c hX ξ)).1.left ⟶
      (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueSndFiber Λ k c hX ξ)).1.left :=
  FlatAlgebraCat.Hom.of
    (eqToHom ((glueingComparison_fst_base Λ k c hX ξ).trans
      (glueingComparison_snd_base Λ k c hX ξ).symm))
    (glueingComparisonRingHom Λ k c hX ξ) sorry sorry

/-- Inverse morphism of restricted overlap algebras in `FlatAlgebraCat`. -/
def glueingComparisonAlgebraInv (ξ : deformationCategory Λ k hX) :
    (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueSndFiber Λ k c hX ξ)).1.left ⟶
      (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueFstFiber Λ k c hX ξ)).1.left :=
  FlatAlgebraCat.Hom.of
    (eqToHom ((glueingComparison_snd_base Λ k c hX ξ).trans
      (glueingComparison_fst_base Λ k c hX ξ).symm))
    (glueingComparisonRingHom_inv Λ k c hX ξ) sorry sorry

/-- Ambient isomorphism of overlap algebras in `FlatAlgebraCat`. -/
def glueingComparisonAlgebraIso (ξ : deformationCategory Λ k hX) :
    (((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueFstFiber Λ k c hX ξ)).1.left ≅
      (((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj
        (glueSndFiber Λ k c hX ξ)).1.left where
  hom := glueingComparisonAlgebraHom Λ k c hX ξ
  inv := glueingComparisonAlgebraInv Λ k c hX ξ
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Comparison isomorphism in `Def_{P₁₂}` between the two restricted ring deformations. -/
def glueingComparisonIso (ξ : deformationCategory Λ k hX) :
    ((restrictRing₁ Λ k c hX).fiberFunctor ξ.left.base).obj (glueFstFiber Λ k c hX ξ) ≅
      ((restrictRing₂ Λ k c hX).fiberFunctor ξ.left.base).obj (glueSndFiber Λ k c hX ξ) :=
  Functor.Fiber.isoMk (Over.isoMk (glueingComparisonAlgebraIso Λ k c hX ξ) sorry) sorry

/-- The image of a deformation of `X` in the 2-fiber product of ring deformation categories. -/
def glueingObj (ξ : deformationCategory Λ k hX) :
    (ringDeformationPullback Λ k c hX).obj :=
  BasedCategory.PseudoPullback.mk (restrictRing₁ Λ k c hX) (restrictRing₂ Λ k c hX) ξ.left.base
    { fst := glueFstFiber Λ k c hX ξ
      snd := glueSndFiber Λ k c hX ξ
      iso := glueingComparisonIso Λ k c hX ξ }

/-- A morphism of deformations of `X` induces a morphism of 2-fiber product objects. -/
def glueingMap {ξ η : deformationCategory Λ k hX} (φ : ξ ⟶ η) :
    glueingObj Λ k c hX ξ ⟶ glueingObj Λ k c hX η :=
  BasedCategory.PseudoPullback.Hom.mk
    ((schemeForget Λ k hX).map φ)
    (glueFstMap Λ k c hX φ) sorry
    (glueSndMap Λ k c hX φ) sorry
    sorry

/-- The ordinary functor `Def_X ⥤ Def_{P₁} ×_{Def_{P₁₂}} Def_{P₂}`. -/
def glueingFunctor :
    deformationCategory Λ k hX ⥤ (ringDeformationPullback Λ k c hX).obj where
  obj := glueingObj Λ k c hX
  map := glueingMap Λ k c hX
  map_id := sorry
  map_comp := sorry

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
  sorry

/-- `glueingBasedFunctor` commutes strictly with the projections to `ArtinianLocalAlgCat`. -/
theorem glueingBasedFunctor_w :
    (glueingBasedFunctor Λ k c hX).toFunctor.comp (ringDeformationPullback Λ k c hX).p =
      schemeForget Λ k hX :=
  sorry

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
