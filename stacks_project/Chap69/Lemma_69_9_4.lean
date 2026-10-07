module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import stacks_project.Chap69.Lemma_69_9_4_Pushforward
public import stacks_project.Chap69.Lemma_69_9_4_Supported

/-!
# Lemma 69.9.4

For a closed immersion of algebraic spaces, `Ri_* = i_*` induces an equivalence
`D(Z_étale) ≃ D_|Z|(X_étale)` whose quasi-inverse is the restriction of `i⁻¹`,
which agrees there with `Rℋ_Z`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Functor.RightDerived

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
variable [Etale (closedImmersionComplementι i)]
variable [Abelian (EtaleSheaf X)] [Abelian (EtaleSheaf Z)]
variable [Abelian (EtaleSheaf (closedImmersionComplement i))]
variable [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
variable [HasSheafify (smallEtaleTopology Z) AddCommGrpCat.{u + 1}]
variable [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory (EtaleSheaf Z)]
variable [(sheafPushforward AddCommGrpCat.{u + 1} i).Additive]
variable [(sheafInverseImage AddCommGrpCat.{u + 1} i).Additive]

/-- Lemma 69.9.4 (1): for a closed immersion of algebraic spaces, the small-étale derived
direct image `Ri_*` coincides with the underived functor `i_*`, as any right-derived
model of `sheafPushforward i` is isomorphic to `etaleDerivedDirectImage i`. -/
@[stacks 0AEI]
def closedImmersion_etaleDerivedDirectImage_eq_underived
    (closedModel : EtaleRightDerivedModel (sheafPushforward AddCommGrpCat.{u + 1} i)) :
    closedModel.functor ≅ etaleDerivedDirectImage i :=
  closedModel.iso (etaleDerivedDirectImage_rightDerivedModel i)

/-- Objectwise, any right-derived model of `sheafPushforward i` agrees with
`etaleDerivedDirectImage i`. -/
def closedImmersion_etaleDerivedDirectImage_eq_underived_app
    (closedModel : EtaleRightDerivedModel (sheafPushforward AddCommGrpCat.{u + 1} i))
    (K : EtaleDerived Z) :
    closedModel.functor.obj K ≅ (etaleDerivedDirectImage i).obj K :=
  (closedImmersion_etaleDerivedDirectImage_eq_underived i closedModel).app K

/-- Lemma 69.9.4 (2): the underived/derived small-étale direct image of a closed
immersion induces an equivalence `D(Z_étale) ≃ D_|Z|(X_étale)`. -/
@[stacks 0AEI]
theorem closedImmersion_etaleDerivedDirectImage_equivalence :
    (etaleDerivedDirectImage.toSupported i).IsEquivalence :=
  sorry

/-- Lemma 69.9.4 (3): on `D_|Z|(X_étale)`, the quasi-inverse of lifted small-étale
direct image is the restriction of `i⁻¹`. -/
@[stacks 0AEI]
def closedImmersion_etaleSupported_quasiInverse :
    (etaleDerivedDirectImage.toSupported i).inv ≅ etaleDerivedSupported.inverseImage i :=
  Adjunction.leftAdjointUniq
    (etaleDerivedDirectImage.toSupported i).asEquivalence.symm.toAdjunction
    (etaleDerivedSupported_inverseImageAdjunction i)

/-- Objectwise, the unspecified inverse of lifted direct image is the restricted
derived inverse image. -/
def closedImmersion_etaleSupported_quasiInverse_app (K : EtaleDerivedSupported i) :
    (etaleDerivedDirectImage.toSupported i).inv.obj K ≅
      (etaleDerivedSupported.inverseImage i).obj K :=
  (closedImmersion_etaleSupported_quasiInverse i).app K

/-- Derived small-étale pushforward along a closed immersion is a left-derived functor of
the homotopy-level pushforward. -/
instance etaleDerivedDirectImage_isLeftDerived :
    (etaleDerivedDirectImage i).IsLeftDerivedFunctor
      (sheafPushforward AddCommGrpCat.{u + 1} i).mapDerivedCategoryFactorsh.hom
      (etaleQuasiIso Z) :=
  sorry

variable (sectionsWithSupport : EtaleSheaf X ⥤ EtaleSheaf Z)
variable [sectionsWithSupport.Additive]

/-- A chosen right-derived model of sections with support is a right-derived functor of
its homotopy-to-derived unit. -/
instance etaleRightDerivedModel_isRightDerived
    (supportModel : EtaleRightDerivedModel sectionsWithSupport) :
    supportModel.functor.IsRightDerivedFunctor supportModel.unit (etaleQuasiIso X) :=
  supportModel.isRightDerived

/-- The composite `i_* ⋙ Rℋ_Z` remains left derived after postcomposition with a
right-derived model of sections with support. -/
instance etaleDerivedDirectImage_sections_comp_isLeftDerived
    (supportModel : EtaleRightDerivedModel sectionsWithSupport) :
    (etaleDerivedDirectImage i ⋙ supportModel.functor).IsLeftDerivedFunctor
      ((Functor.associator (etaleDerivedQuotient Z) (etaleDerivedDirectImage i)
          supportModel.functor).inv ≫
        Functor.whiskerRight
          (sheafPushforward AddCommGrpCat.{u + 1} i).mapDerivedCategoryFactorsh.hom
          supportModel.functor)
      (etaleQuasiIso Z) :=
  sorry

/-- The composite `Rℋ_Z ⋙ i_*` remains right derived after postcomposition with derived
small-étale pushforward. -/
instance etaleDerivedDirectImage_sections_comp_isRightDerived
    (supportModel : EtaleRightDerivedModel sectionsWithSupport) :
    (supportModel.functor ⋙ etaleDerivedDirectImage i).IsRightDerivedFunctor
      (Functor.whiskerRight supportModel.unit (etaleDerivedDirectImage i) ≫
        (Functor.associator (etaleDerivedQuotient X) supportModel.functor
          (etaleDerivedDirectImage i)).hom)
      (etaleQuasiIso X) :=
  sorry

/-- Derived adjunction `i_* ⊣ Rℋ_Z` induced by an additive right adjoint of the exact
closed-immersion pushforward and a chosen right-derived model of `ℋ_Z`. -/
def etaleDerivedDirectImage_sectionsAdjunction
    (adj : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupport)
    (supportModel : EtaleRightDerivedModel sectionsWithSupport) :
    etaleDerivedDirectImage i ⊣ supportModel.functor :=
  (Adjunction.mapHomotopyCategoryAdjunction adj).derived
    (etaleQuasiIso Z) (etaleQuasiIso X)
    (sheafPushforward AddCommGrpCat.{u + 1} i).mapDerivedCategoryFactorsh.hom
    supportModel.unit

/-- Restriction of `i_* ⊣ Rℋ_Z` to the supported subcategory `D_|Z|(X_étale)`. -/
def etaleDerivedSupported_sectionsModelAdjunction
    (adj : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupport)
    (supportModel : EtaleRightDerivedModel sectionsWithSupport) :
    etaleDerivedDirectImage.toSupported i ⊣
      EtaleDerivedSupported.inclusion i ⋙ supportModel.functor :=
  (etaleDerivedDirectImage_sectionsAdjunction i sectionsWithSupport adj
      supportModel).restrictFullyFaithful
    (Functor.FullyFaithful.id _)
    (etaleDerivedSupportedOn i).fullyFaithfulι
    (etaleDerivedDirectImage.toSupportedCompιIso i).symm
    (Functor.rightUnitor
      (EtaleDerivedSupported.inclusion i ⋙ supportModel.functor))

/-- Lemma 69.9.4 (4): on `D_|Z|(X_étale)`, the restriction of `i⁻¹` coincides with the
restriction of derived sections with support `Rℋ_Z`. -/
@[stacks 0AEI]
def closedImmersion_etaleSupported_quasiInverse_sections
    (adj : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupport)
    (supportModel : EtaleRightDerivedModel sectionsWithSupport) :
    etaleDerivedSupported.inverseImage i ≅
      EtaleDerivedSupported.inclusion i ⋙ supportModel.functor :=
  (closedImmersion_etaleSupported_quasiInverse i).symm ≪≫
    Adjunction.rightAdjointUniq
      (etaleDerivedDirectImage.toSupported i).asEquivalence.toAdjunction
      (etaleDerivedSupported_sectionsModelAdjunction i sectionsWithSupport adj supportModel)

/-- Objectwise, restricted derived inverse image agrees with restricted derived
sections with support. -/
def closedImmersion_etaleSupported_quasiInverse_sections_app
    (adj : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupport)
    (supportModel : EtaleRightDerivedModel sectionsWithSupport)
    (K : EtaleDerivedSupported i) :
    (etaleDerivedSupported.inverseImage i).obj K ≅
      (EtaleDerivedSupported.inclusion i ⋙ supportModel.functor).obj K :=
  (closedImmersion_etaleSupported_quasiInverse_sections i sectionsWithSupport adj
    supportModel).app K

variable [PreservesFiniteLimits sectionsWithSupport]
variable [PreservesFiniteColimits sectionsWithSupport]

/-- Restriction of `i_* ⊣ ℋ_Z` to the supported subcategory, after deriving the exact
functor of sections with support. -/
def etaleDerivedSupported_sectionsAdjunction
    (adj : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupport) :
    etaleDerivedDirectImage.toSupported i ⊣
      EtaleDerivedSupported.inclusion i ⋙ sectionsWithSupport.mapDerivedCategory :=
  (Adjunction.mapDerivedCategory adj).restrictFullyFaithful
    (Functor.FullyFaithful.id _)
    (etaleDerivedSupportedOn i).fullyFaithfulι
    (etaleDerivedDirectImage.toSupportedCompιIso i).symm
    (Functor.rightUnitor
      (EtaleDerivedSupported.inclusion i ⋙ sectionsWithSupport.mapDerivedCategory))

/-- Morphisms into a supported object correspond to morphisms into derived sections with
support, via `etaleDerivedSupported_sectionsAdjunction`. -/
theorem etaleDerivedSupported_sectionsAdjunction_homEquiv_apply
    (adj : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupport)
    {K : EtaleDerived Z} {L : EtaleDerivedSupported i}
    (f : (etaleDerivedDirectImage.toSupported i).obj K ⟶ L) :
    (etaleDerivedSupported_sectionsAdjunction i sectionsWithSupport adj).homEquiv K L f =
      (etaleDerivedSupported_sectionsAdjunction i sectionsWithSupport adj).unit.app K ≫
        (EtaleDerivedSupported.inclusion i ⋙
          sectionsWithSupport.mapDerivedCategory).map f :=
  sorry

/-- The exact presentation of `sectionsWithSupport` as an explicit right-derived model. -/
def sectionsWithSupport_etaleRightDerivedModel :
    EtaleRightDerivedModel sectionsWithSupport :=
  Model.of
    sectionsWithSupport.mapDerivedCategory
    sectionsWithSupport.mapDerivedCategoryFactorsh.inv
    (Exact.isRightDerived sectionsWithSupport)

/-- The exact derived functor of sections with support is the functor of the associated
right-derived model. -/
theorem sectionsWithSupport_etaleRightDerivedModel_functor :
    (sectionsWithSupport_etaleRightDerivedModel sectionsWithSupport).functor =
      sectionsWithSupport.mapDerivedCategory :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
