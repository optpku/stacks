module

public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Sites.Continuous
public import stacks_project.Chap63.Lemma_63_6_2
public import stacks_project.Chap63.Lemma_63_6_3

/-!
# Compatibility of étale upper shriek with restriction

Lemma 63.6.4: for étale morphisms `j : U ⟶ X` and `j' : V ⟶ U`, the
composition isomorphism of inverse images agrees with the composition
isomorphism of upper shrieks after identifying `j^!` with `j⁻¹`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [LocallyQuasiFinite j]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]

/-- The identification of `upperShriek j` with étale restriction
`etaleRestrictionSheaf j AddCommGrpCat`, obtained by uniqueness of right
adjoints of `lowerShriek j`. -/
def upperShriekRestrictionIso :
    upperShriek j ≅ etaleRestrictionSheaf j AddCommGrpCat.{u} :=
  lowerShriek_rightAdjointIsoRestriction j (lowerShriekAdjunction j)

/-- `upperShriekRestrictionIso` evaluated at an abelian étale sheaf. -/
def upperShriekRestrictionIso_app
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (upperShriek j).obj G ≅
      (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj G :=
  (upperShriekRestrictionIso j).app G

/-- `upperShriekRestrictionIso` is the uniqueness isomorphism of
`lowerShriekAdjunction` against étale restriction. -/
theorem upperShriekRestrictionIso_eq :
    upperShriekRestrictionIso j =
      lowerShriek_rightAdjointIsoRestriction j (lowerShriekAdjunction j) :=
  sorry

variable {V : Scheme.{u}} (j' : V ⟶ U) [Etale j']

/-- Site-level identification of étale restriction along `j' ≫ j` with the
composite of the restrictions along `j'` and `j`. -/
def etaleRestrictionFunctorCompIso :
    etaleRestriction (j' ≫ j) ≅ etaleRestriction j' ⋙ etaleRestriction j :=
  MorphismProperty.Over.mapComp (⊤ : MorphismProperty Scheme)
    (inferInstance : Etale j') (inferInstance : Etale j) (j' ≫ j) rfl

/-- `etaleRestrictionFunctorCompIso` is the `Over.mapComp` isomorphism. -/
theorem etaleRestrictionFunctorCompIso_eq :
    etaleRestrictionFunctorCompIso j j' =
      MorphismProperty.Over.mapComp (⊤ : MorphismProperty Scheme)
        (inferInstance : Etale j') (inferInstance : Etale j) (j' ≫ j) rfl :=
  sorry

variable [LocallyQuasiFinite j'] [LocallyOfFiniteType j] [LocallyOfFiniteType j']
variable [∀ F : V.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j').op.HasLeftKanExtension F]
variable [∀ F : V.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (j' ≫ j)).op.HasLeftKanExtension F]
variable [HasSheafify U.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasCoproducts.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]

/-- Sheaf-level inverse-image composition
`(j ∘ j')⁻¹ ≅ (j')⁻¹ ∘ j⁻¹`, matching the direction of
`upperShriekCompIso j' j`. -/
def etaleRestrictionSheaf_compIso :
    etaleRestrictionSheaf (j' ≫ j) AddCommGrpCat.{u} ≅
      etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙
        etaleRestrictionSheaf j' AddCommGrpCat.{u} :=
  (sheafPushforwardContinuousComp'
      (etaleRestrictionFunctorCompIso j j').symm AddCommGrpCat.{u}
      V.smallEtaleTopology U.smallEtaleTopology X.smallEtaleTopology).symm

/-- `etaleRestrictionSheaf_compIso` is the inverse of continuous sheaf
pushforward composition along `etaleRestrictionFunctorCompIso`. -/
theorem etaleRestrictionSheaf_compIso_eq :
    etaleRestrictionSheaf_compIso j j' =
      (sheafPushforwardContinuousComp'
          (etaleRestrictionFunctorCompIso j j').symm AddCommGrpCat.{u}
          V.smallEtaleTopology U.smallEtaleTopology
          X.smallEtaleTopology).symm :=
  sorry

/-- `etaleRestrictionSheaf_compIso` evaluated at an abelian étale sheaf. -/
def etaleRestrictionSheaf_compIso_app
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (etaleRestrictionSheaf (j' ≫ j) AddCommGrpCat.{u}).obj G ≅
      (etaleRestrictionSheaf j' AddCommGrpCat.{u}).obj
        ((etaleRestrictionSheaf j AddCommGrpCat.{u}).obj G) :=
  (etaleRestrictionSheaf_compIso j j').app G

/-- Whiskered Lemma 63.6.2 identifications on a composite of upper shrieks. -/
def upperShriekRestrictionIso_comp :
    upperShriek j ⋙ upperShriek j' ≅
      etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙
        etaleRestrictionSheaf j' AddCommGrpCat.{u} :=
  isoWhiskerRight (upperShriekRestrictionIso j) (upperShriek j') ≪≫
    isoWhiskerLeft (etaleRestrictionSheaf j AddCommGrpCat.{u})
      (upperShriekRestrictionIso j')

/-- Shriek-composition, then the whiskered identification with restriction. -/
def upperShriekCompIso_restriction_left :
    upperShriek (j' ≫ j) ⟶
      etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙
        etaleRestrictionSheaf j' AddCommGrpCat.{u} :=
  (upperShriekCompIso j' j).hom ≫ (upperShriekRestrictionIso_comp j j').hom

/-- Identification of the composite shriek, then inverse-image composition. -/
def upperShriekCompIso_restriction_right :
    upperShriek (j' ≫ j) ⟶
      etaleRestrictionSheaf j AddCommGrpCat.{u} ⋙
        etaleRestrictionSheaf j' AddCommGrpCat.{u} :=
  (upperShriekRestrictionIso (j' ≫ j)).hom ≫
    (etaleRestrictionSheaf_compIso j j').hom

/-- Lemma 63.6.4: Let `j : U ⟶ X` and `j' : V ⟶ U` be étale morphisms.
The isomorphism `(j ∘ j')⁻¹ ≅ (j')⁻¹ ∘ j⁻¹` given by
`etaleRestrictionSheaf_compIso` and the isomorphism
`(j ∘ j')^! ≅ (j')^! ∘ j^!` of Lemma 63.6.3 given by
`upperShriekCompIso j' j` agree via the identification
`upperShriekRestrictionIso` of Lemma 63.6.2. -/
@[stacks 0F5C]
theorem upperShriekCompIso_restriction :
    upperShriekCompIso_restriction_left j j' =
      upperShriekCompIso_restriction_right j j' :=
  sorry

/-- Objectwise form of `upperShriekCompIso_restriction` at an abelian étale
sheaf. -/
theorem upperShriekCompIso_restriction_app
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    (upperShriekCompIso_restriction_left j j').app G =
      (upperShriekCompIso_restriction_right j j').app G :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
