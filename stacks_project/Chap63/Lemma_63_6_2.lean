module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import stacks_project.Chap63.Definition_63_4_4_LowerShriek
public import stacks_project.Chap63.Lemma_63_4_3

/-!
# Étale inverse image as the right adjoint of finite-support lower shriek

Lemma 63.6.2: for an étale morphism `j : U ⟶ X`, uniqueness of adjoints
identifies the right adjoint of finite-support `lowerShriek j` with étale
restriction, so `j^!` agrees with `j⁻¹`.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] [LocallyQuasiFinite j]
variable [∀ F : U.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction j).op.HasLeftKanExtension F]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]

/-- Lemma 63.6.2: Let `j : U ⟶ X` be an étale morphism. Then the right adjoint
of finite-support `lowerShriek j` agrees with étale restriction
`etaleRestrictionSheaf j AddCommGrpCat`, so `j^!` coincides with `j⁻¹`. -/
@[stacks 0F5A]
def lowerShriekRestrictionAdjunction :
    lowerShriek j ⊣ etaleRestrictionSheaf j AddCommGrpCat.{u} :=
  (abelianExtensionByZero_adjunction j).ofNatIsoLeft
    (extensionByZeroIsoLowerShriek j)

/-- Any right adjoint of `lowerShriek j` is canonically isomorphic to étale
restriction. -/
def lowerShriek_rightAdjointIsoRestriction
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf U.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : lowerShriek j ⊣ G) :
    G ≅ etaleRestrictionSheaf j AddCommGrpCat.{u} :=
  adj.rightAdjointUniq (lowerShriekRestrictionAdjunction j)

/-- The uniqueness isomorphism identifying a right adjoint of `lowerShriek j`
with étale restriction, evaluated at an abelian étale sheaf. -/
def lowerShriek_rightAdjointIsoRestriction_app
    {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf U.smallEtaleTopology AddCommGrpCat.{u}}
    (adj : lowerShriek j ⊣ G)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    G.obj F ≅ (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj F :=
  (lowerShriek_rightAdjointIsoRestriction j adj).app F

/-- Hom-sets of the adjunction `lowerShriek j ⊣ etaleRestrictionSheaf j AddCommGrpCat`. -/
def lowerShriekRestrictionAdjunction_homEquiv
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :
    ((lowerShriek j).obj F ⟶ G) ≃
      (F ⟶ (etaleRestrictionSheaf j AddCommGrpCat.{u}).obj G) :=
  (lowerShriekRestrictionAdjunction j).homEquiv F G

/-- The adjunction is the transport of étale extension-by-zero along the
identification of Lemma 63.4.3. -/
theorem lowerShriekRestrictionAdjunction_eq :
    lowerShriekRestrictionAdjunction j =
      (abelianExtensionByZero_adjunction j).ofNatIsoLeft
        (extensionByZeroIsoLowerShriek j) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
