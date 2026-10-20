/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsSupportedIn

/-!
# Excision for supported étale sections

An étale morphism identifying a closed subscheme with a closed image induces
a canonical additive equivalence of sections supported in those subschemes.
-/

public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
variable {U U' : X.Etale} (φ : U' ⟶ U) {Z' : Scheme.{u}} (ι : Z' ⟶ U'.left)
variable [IsClosedImmersion ι] [IsClosedImmersion (ι ≫ φ.left)]

namespace SupportExcision

/-- The portion of the inverse image of the composite closed image outside the original image. -/
private def residualClosedSet : Set U'.left :=
  (φ.left ⁻¹' Set.range (ι ≫ φ.left)) \ Set.range ι

/-- The complement of the residual closed set is open. -/
private theorem isOpen_compl_residualClosedSet :
    IsOpen (residualClosedSet φ ι)ᶜ := sorry

/-- The open complement of the residual closed set. -/
private def residualOpen : U'.left.Opens :=
  ⟨(residualClosedSet φ ι)ᶜ, isOpen_compl_residualClosedSet φ ι⟩

/-- The open complement of the residual closed set as an object of the small étale site. -/
private abbrev residualEtale : X.Etale :=
  mk ((residualOpen φ ι).ι ≫ U'.hom)

/-- The open immersion of the residual open as a morphism of the small étale site. -/
private abbrev residualHom : residualEtale φ ι ⟶ U' :=
  MorphismProperty.Over.homMk (residualOpen φ ι).ι

/-- The composite of the residual open immersion with the given étale-site morphism. -/
private abbrev residualHomOver : residualEtale φ ι ⟶ U :=
  residualHom φ ι ≫ φ

/-- The inverse image of the original closed image on the residual open. -/
private def residualSupport : Set (residualEtale φ ι).left :=
  (residualOpen φ ι).ι ⁻¹' Set.range ι

/-- Restriction of sections supported in the original closed image to the residual open. -/
private def restrictSupportedInResidual :
    abelianSheafSectionsSupportedIn F U' (Set.range ι) →+
      abelianSheafSectionsSupportedIn F (residualEtale φ ι) (residualSupport φ ι) :=
  restrictSupportedIn F (residualHom φ ι) (Set.range ι)

/-- Restriction from the composite closed image lands in the supported sections on the residual open. -/
private theorem restrictOver_mem
    (σ : abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left))) :
    F.1.map (residualHomOver φ ι).op σ.val ∈
      abelianSheafSectionsSupportedIn F (residualEtale φ ι) (residualSupport φ ι) := sorry

/-- Restriction of sections supported in the composite closed image to the residual open. -/
private def restrictSupportedInResidualOver :
    abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left)) →+
      abelianSheafSectionsSupportedIn F (residualEtale φ ι) (residualSupport φ ι) :=
  ((F.1.map (residualHomOver φ ι).op).hom.restrict
    (abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left)))).codRestrict
    (abelianSheafSectionsSupportedIn F (residualEtale φ ι) (residualSupport φ ι))
    (restrictOver_mem F φ ι)

/-- Restriction to the residual open is bijective on sections supported in the original closed image. -/
private theorem restrictSupportedInResidual_bijective :
    Function.Bijective (restrictSupportedInResidual F φ ι) := sorry

/-- Restriction to the residual open is bijective on sections supported in the composite closed image. -/
private theorem restrictSupportedInResidualOver_bijective :
    Function.Bijective (restrictSupportedInResidualOver F φ ι) := sorry

end SupportExcision

/-- An étale morphism identifying a closed subscheme with a closed image induces a canonical
additive equivalence between the corresponding groups of supported sections. -/
def abelianSheafSectionsSupportedInAddEquiv :
    abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left)) ≃+
      abelianSheafSectionsSupportedIn F U' (Set.range ι) :=
  let overEquiv :
      abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left)) ≃+
        abelianSheafSectionsSupportedIn F (SupportExcision.residualEtale φ ι)
          (SupportExcision.residualSupport φ ι) :=
    { toFun := SupportExcision.restrictSupportedInResidualOver F φ ι
      invFun := Function.invFun (SupportExcision.restrictSupportedInResidualOver F φ ι)
      left_inv := Function.leftInverse_invFun
        (SupportExcision.restrictSupportedInResidualOver_bijective F φ ι).injective
      right_inv := Function.rightInverse_invFun
        (SupportExcision.restrictSupportedInResidualOver_bijective F φ ι).surjective
      map_add' := (SupportExcision.restrictSupportedInResidualOver F φ ι).map_add }
  let residualEquiv :
      abelianSheafSectionsSupportedIn F U' (Set.range ι) ≃+
        abelianSheafSectionsSupportedIn F (SupportExcision.residualEtale φ ι)
          (SupportExcision.residualSupport φ ι) :=
    { toFun := SupportExcision.restrictSupportedInResidual F φ ι
      invFun := Function.invFun (SupportExcision.restrictSupportedInResidual F φ ι)
      left_inv := Function.leftInverse_invFun
        (SupportExcision.restrictSupportedInResidual_bijective F φ ι).injective
      right_inv := Function.rightInverse_invFun
        (SupportExcision.restrictSupportedInResidual_bijective F φ ι).surjective
      map_add' := (SupportExcision.restrictSupportedInResidual F φ ι).map_add }
  overEquiv.trans residualEquiv.symm

/-- If the inverse-image support equals the original closed image, the canonical comparison
of supported sections is restriction along the étale-site morphism. -/
theorem abelianSheafSectionsSupportedInAddEquiv_apply_of_preimage_eq
    (h_preimage : φ.left ⁻¹' Set.range (ι ≫ φ.left) = Set.range ι)
    (σ : abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left))) :
    (abelianSheafSectionsSupportedInAddEquiv F φ ι σ).val = F.1.map φ.op σ.val := sorry

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

/-- Unique extension of sections supported on a closed subscheme along a
morphism of small étale objects, via the inverse of
`abelianSheafSectionsSupportedInAddEquiv`. -/
@[expose] def extendSupportedAlongOpen {U U' : X.Etale} (φ : U' ⟶ U) {Z' : Scheme.{u}}
    (ι : Z' ⟶ U'.left) [IsClosedImmersion ι]
    (h_closed : IsClosedImmersion (ι ≫ φ.left)) :
    abelianSheafSectionsSupportedIn F U' (Set.range ι) →+
      abelianSheafSectionsSupportedIn F U (Set.range (ι ≫ φ.left)) :=
  AddEquiv.toAddMonoidHom
    (@abelianSheafSectionsSupportedInAddEquiv _ F _ _ φ _ ι inferInstance
      h_closed).symm

/-- Unique extension along an open acts by the inverse supported-section
equivalence. -/
theorem extendSupportedAlongOpen_apply {U U' : X.Etale} (φ : U' ⟶ U)
    {Z' : Scheme.{u}} (ι : Z' ⟶ U'.left) [IsClosedImmersion ι]
    (h_closed : IsClosedImmersion (ι ≫ φ.left))
    (σ : abelianSheafSectionsSupportedIn F U' (Set.range ι)) :
    extendSupportedAlongOpen F φ ι h_closed σ =
      (@abelianSheafSectionsSupportedInAddEquiv _ F _ _ φ _ ι inferInstance
        h_closed).symm σ :=
  rfl

end AlgebraicGeometry.Scheme.Etale

end
