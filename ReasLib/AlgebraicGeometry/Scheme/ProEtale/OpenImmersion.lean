module

public import ReasLib.AlgebraicGeometry.Scheme.ProEtale.DirectImage
public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import ReasLib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u u₁ v₁

namespace AlgebraicGeometry.Scheme

namespace ProEt

variable {U X : Scheme.{u}}

/-- Postcomposition with an open immersion is full on small pro-étale sites. -/
instance restriction_full_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j] :
    (restriction j).Full :=
  sorry

/-- Postcomposition with an open immersion is faithful on small pro-étale sites. -/
instance restriction_faithful_of_isOpenImmersion (j : U ⟶ X) [IsOpenImmersion j] :
    (restriction j).Faithful :=
  sorry

/-- The proposition that pro-étale restriction along an open immersion is fully
faithful. -/
theorem restrictionFullyFaithful_of_isOpenImmersion
    (j : U ⟶ X) [IsOpenImmersion j] :
    Nonempty (restriction j).FullyFaithful :=
  ⟨Functor.FullyFaithful.ofFullyFaithful (restriction j)⟩

variable (j : U ⟶ X) [IsOpenImmersion j]
variable (A : Type u₁) [Category.{v₁} A]

/-- For an open immersion of schemes, the unit of the extension-by-zero and
restriction adjunction is an isomorphism. -/
@[stacks 09BN, instance]
instance extensionByZero_unit_isIso_of_isOpenImmersion
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology U) A] [HasWeakSheafify (topology X) A]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseLeftKanExtension F]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseRightKanExtension F] :
    IsIso (extensionByZero_adjunction j A).unit :=
  sorry

/-- For an open immersion of schemes, the counit of the restriction and
direct-image adjunction is an isomorphism. -/
@[stacks 09BN, instance]
instance directImage_counit_isIso_of_isOpenImmersion
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseRightKanExtension F] :
    IsIso (directImage_adjunction j A).counit :=
  sorry

/-- The proposition that extension by zero along an open immersion of schemes
is fully faithful. -/
@[stacks 09BN]
theorem extensionByZeroFullyFaithful_of_isOpenImmersion
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology U) A] [HasWeakSheafify (topology X) A]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseLeftKanExtension F]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseRightKanExtension F] :
    Nonempty (extensionByZero j A).FullyFaithful :=
  ⟨(extensionByZero_adjunction j A).fullyFaithfulLOfIsIsoUnit⟩

/-- The proposition that direct image along an open immersion of schemes is
fully faithful. -/
@[stacks 09BN]
theorem directImageFullyFaithful_of_isOpenImmersion
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseRightKanExtension F] :
    Nonempty (directImage j A).FullyFaithful :=
  ⟨(directImage_adjunction j A).fullyFaithfulROfIsIsoCounit⟩

/-- The canonical isomorphism `id ≅ j⁻¹ j_!` along an open immersion of schemes:
the unit of the extension-by-zero/restriction adjunction. -/
def idIso_extensionByZero_comp_restrictionSheaf
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology U) A] [HasWeakSheafify (topology X) A]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseLeftKanExtension F]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseRightKanExtension F] :
    𝟭 (Sheaf (topology U) A) ≅ extensionByZero j A ⋙ restrictionSheaf j A :=
  asIso (extensionByZero_adjunction j A).unit

/-- The forward map of `id ≅ j⁻¹ j_!` is the adjunction unit. -/
@[simp]
theorem idIso_extensionByZero_comp_restrictionSheaf_hom
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasLeftKanExtension F]
    [HasWeakSheafify (topology U) A] [HasWeakSheafify (topology X) A]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseLeftKanExtension F]
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseRightKanExtension F] :
    (idIso_extensionByZero_comp_restrictionSheaf j A).hom =
      (extensionByZero_adjunction j A).unit :=
  rfl

/-- The canonical isomorphism `j⁻¹ j_* ≅ id` along an open immersion of schemes:
the counit of the restriction/direct-image adjunction. -/
def directImage_comp_restrictionSheaf_isoId
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseRightKanExtension F] :
    directImage j A ⋙ restrictionSheaf j A ≅ 𝟭 (Sheaf (topology U) A) :=
  asIso (directImage_adjunction j A).counit

/-- The forward map of `j⁻¹ j_* ≅ id` is the adjunction counit. -/
@[simp]
theorem directImage_comp_restrictionSheaf_isoId_hom
    [∀ F : U.ProEtᵒᵖ ⥤ A, (restriction j).op.HasPointwiseRightKanExtension F] :
    (directImage_comp_restrictionSheaf_isoId j A).hom =
      (directImage_adjunction j A).counit :=
  rfl

end ProEt

end AlgebraicGeometry.Scheme
