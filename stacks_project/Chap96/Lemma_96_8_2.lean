module

public import stacks_project.Chap96.Lemma_96_8_2_Comparison
public import ReasLib.CategoryTheory.Fibered.Representable.Presentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 96.8.2

If a 1-morphism of categories fibred in groupoids over a scheme is representable
by a morphism of schemes, the induced morphism of associated ringed topoi agrees
with the morphism of big ringed topoi of that scheme morphism, via the
identifications of Lemma 96.8.1.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {𝒳 𝒴 : GroupoidsOver S} {X Y : Over S}
variable (eX : 𝒳 ≌ slice X) (eY : 𝒴 ≌ slice Y) (f : 𝒳 ⟶ 𝒴) (τ : StandardTopology)
variable [HasSheafify (associatedRingedSite 𝒳 τ).siteTopology (Type u)]
variable [HasSheafify (associatedRingedSite 𝒴 τ).siteTopology (Type u)]
variable [HasSheafify (associatedRingedSite (slice X) τ).siteTopology (Type u)]
variable [HasSheafify (associatedRingedSite (slice Y) τ).siteTopology (Type u)]
variable [HasSheafify (τ.overTopology X.left) (Type u)]
variable [∀ P : 𝒳.totalᵒᵖ ⥤ Type u, (toFunctor f).op.HasPointwiseRightKanExtension P]
variable [∀ P : 𝒳.totalᵒᵖ ⥤ Type u, (toFunctor eX.hom).op.HasPointwiseRightKanExtension P]
variable [∀ P : 𝒴.totalᵒᵖ ⥤ Type u, (toFunctor eY.hom).op.HasPointwiseRightKanExtension P]
variable [∀ P : (associatedRingedSite (slice X) τ).carrierᵒᵖ ⥤ Type u,
    X.iteratedSliceForward.op.HasPointwiseRightKanExtension P]
variable [∀ P : (associatedRingedSite (slice Y) τ).carrierᵒᵖ ⥤ Type u,
    Y.iteratedSliceForward.op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over X.left)ᵒᵖ ⥤ Type u,
    (Over.map (Presentation.recover eX eY f).left).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over X.left)ᵒᵖ ⥤ RingCat.{u},
    (Over.map (Presentation.recover eX eY f).left).op.HasPointwiseRightKanExtension P]
variable [(forget RingCat.{u}).PreservesRightKanExtensions
    (Over.map (Presentation.recover eX eY f).left).op]

/-- Lemma 96.8.2: let `S` be a scheme and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over `S`. Assume `𝒳` and `𝒴` are representable by
schemes, exhibited by equivalences `eX : 𝒳 ≌ slice X` and `eY : 𝒴 ≌ slice Y`.
Let `Presentation.recover eX eY f` be the corresponding morphism of schemes over
`S`. For each standard topology `τ ∈ {Zariski, étale, smooth, syntomic, fppf}`,
the morphism of ringed topoi `associatedRingedToposHom f τ` agrees with the
morphism of ringed topoi
`StandardTopology.Big.ringedToposHom τ (Presentation.recover eX eY f).left` via
the identifications `associatedRingedSiteToposHom` of Lemma 96.8.1. -/
@[stacks 075J]
def associatedRingedToposHom_comp :
    RingedSite.ToposHom.CommSquare
      (associatedRingedSite 𝒳 τ) (associatedRingedSite 𝒴 τ)
      (StandardTopology.Big.ringedSite τ X.left)
      (StandardTopology.Big.ringedSite τ Y.left) where
  upper := associatedRingedToposHom f τ
  left := associatedRingedSiteToposHom eX τ
  right := associatedRingedSiteToposHom eY τ
  lower := StandardTopology.Big.ringedToposHom τ
    (Presentation.recover eX eY f).left
  cell :=
    { homIso := associatedRingedToposHom_comp_homIso eX eY f τ
      comm := associatedRingedToposHom_comp_homIso_comm eX eY f τ }

/-- The upper edge of `associatedRingedToposHom_comp` is the associated morphism of
ringed topoi of `f`. -/
theorem associatedRingedToposHom_comp_upper :
    (associatedRingedToposHom_comp eX eY f τ).upper = associatedRingedToposHom f τ :=
  sorry

/-- The left edge of `associatedRingedToposHom_comp` is the Lemma 96.8.1 identification
of `𝒳`. -/
theorem associatedRingedToposHom_comp_left :
    (associatedRingedToposHom_comp eX eY f τ).left =
      associatedRingedSiteToposHom eX τ :=
  sorry

/-- The right edge of `associatedRingedToposHom_comp` is the Lemma 96.8.1 identification
of `𝒴`. -/
theorem associatedRingedToposHom_comp_right :
    (associatedRingedToposHom_comp eX eY f τ).right =
      associatedRingedSiteToposHom eY τ :=
  sorry

/-- The lower edge of `associatedRingedToposHom_comp` is the big-site morphism of
ringed topoi of the corresponding scheme morphism. -/
theorem associatedRingedToposHom_comp_lower :
    (associatedRingedToposHom_comp eX eY f τ).lower =
      StandardTopology.Big.ringedToposHom τ
        (Presentation.recover eX eY f).left :=
  sorry

/-- The stored `2`-cell of `associatedRingedToposHom_comp` is
`associatedRingedToposHom_comp_homIso`. -/
theorem associatedRingedToposHom_comp_homIso_eq :
    (associatedRingedToposHom_comp eX eY f τ).cell.homIso =
      associatedRingedToposHom_comp_homIso eX eY f τ :=
  sorry

end AlgebraicGeometry.GroupoidsOver


