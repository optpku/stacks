module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_5_Pullback
public import stacks_project.Chap66.Lemma_66_18_8_Topos

/-!
# Descent of small étale sheaves along a presenting atlas

A surjective étale atlas `φ : U ⟶ X` of an algebraic space yields kernel-pair
projections and a singleton covering of `X_spaces,étale`. Pullback of small étale
sheaves along `φ` is identified with descent data for that covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- The object of `X_spaces,étale` given by an étale atlas `φ : U ⟶ X`. -/
def atlasObj (φ : ofOver U ⟶ X) [Etale φ] : spacesEtaleSite X :=
  MorphismProperty.Over.mk ⊤ φ inferInstance

/-- `atlasObj φ` is the étale slice object with structure morphism `φ`. -/
theorem atlasObj_hom (φ : ofOver U ⟶ X) [Etale φ] : (atlasObj φ).hom = φ :=
  sorry

/-- The structure morphism of `atlasObj φ` toward the terminal object of
`X_spaces,étale`. -/
def atlasToSelf (φ : ofOver U ⟶ X) [Etale φ] : atlasObj φ ⟶ spacesEtaleSite.self X :=
  spacesEtaleSite.homToSelf (atlasObj φ)

/-- `atlasToSelf φ` is `spacesEtaleSite.homToSelf` of the atlas object. -/
theorem atlasToSelf_eq (φ : ofOver U ⟶ X) [Etale φ] :
    atlasToSelf φ = spacesEtaleSite.homToSelf (atlasObj φ) :=
  sorry

/-- The first kernel-pair projection `t = pr0 : U ×_X U ⟶ U`. -/
abbrev relationT (φ : ofOver U ⟶ X) : pullback φ φ ⟶ ofOver U :=
  pullback.fst φ φ

/-- The second kernel-pair projection `s = pr1 : U ×_X U ⟶ U`. -/
abbrev relationS (φ : ofOver U ⟶ X) : pullback φ φ ⟶ ofOver U :=
  pullback.snd φ φ

/-- The first kernel-pair projection of an étale atlas is étale. -/
instance etale_relationT (φ : ofOver U ⟶ X) [Etale φ] : Etale (relationT φ) :=
  inferInstance

/-- The second kernel-pair projection of an étale atlas is étale. -/
instance etale_relationS (φ : ofOver U ⟶ X) [Etale φ] : Etale (relationS φ) :=
  inferInstance

/-- The kernel-pair projections of an atlas equalize `φ`. -/
theorem relationT_comp_atlas (φ : ofOver U ⟶ X) :
    relationT φ ≫ φ = relationS φ ≫ φ :=
  sorry

/-- The first projection `pr0` of the composable-arrow pullback `R ×_{s,t} R`. -/
abbrev relationPr0 (φ : ofOver U ⟶ X) :
    pullback (relationS φ) (relationT φ) ⟶ pullback φ φ :=
  pullback.fst (relationS φ) (relationT φ)

/-- The second projection `pr1` of the composable-arrow pullback `R ×_{s,t} R`. -/
abbrev relationPr1 (φ : ofOver U ⟶ X) :
    pullback (relationS φ) (relationT φ) ⟶ pullback φ φ :=
  pullback.snd (relationS φ) (relationT φ)

/-- The groupoid composition `c : R ×_{s,t} R ⟶ R` of an atlas, as a morphism of
algebraic spaces on the kernel pair. -/
def relationC (φ : ofOver U ⟶ X) :
    pullback (relationS φ) (relationT φ) ⟶ pullback φ φ :=
  pullback.lift (relationPr0 φ ≫ relationT φ) (relationPr1 φ ≫ relationS φ)
    (((Category.assoc (relationPr0 φ) (relationT φ) φ).trans
        (congrArg (fun k ↦ relationPr0 φ ≫ k)
          (pullback.condition : relationT φ ≫ φ = relationS φ ≫ φ))).trans
      ((Category.assoc (relationPr0 φ) (relationS φ) φ).symm.trans
        ((congrArg (fun k ↦ k ≫ φ)
            (pullback.condition :
              relationPr0 φ ≫ relationS φ = relationPr1 φ ≫ relationT φ)).trans
          ((Category.assoc (relationPr1 φ) (relationT φ) φ).trans
            ((congrArg (fun k ↦ relationPr1 φ ≫ k)
                (pullback.condition : relationT φ ≫ φ = relationS φ ≫ φ)).trans
              (Category.assoc (relationPr1 φ) (relationS φ) φ).symm)))))

/-- Composition followed by `t` agrees with `t ∘ pr0`. -/
theorem relationC_comp_relationT (φ : ofOver U ⟶ X) :
    relationC φ ≫ relationT φ = relationPr0 φ ≫ relationT φ :=
  sorry

/-- Composition followed by `s` agrees with `s ∘ pr1`. -/
theorem relationC_comp_relationS (φ : ofOver U ⟶ X) :
    relationC φ ≫ relationS φ = relationPr1 φ ≫ relationS φ :=
  sorry

/-- Inverse image of a small étale sheaf along an étale atlas. -/
abbrev presentationInverseImage (φ : ofOver U ⟶ X)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    Sheaf (smallEtaleTopology (ofOver U)) (Type (u + 1)) :=
  (smallEtaleMorphismOfTopoi φ).inverseImage.obj F

/-- The canonical isomorphism `α : t^{-1} G ≅ s^{-1} G` for `G = φ^{-1} F`, obtained
from functoriality of small étale inverse image and `t ≫ φ = s ≫ φ`. -/
def presentationInverseImageIso (φ : ofOver U ⟶ X)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (smallEtaleMorphismOfTopoi (relationT φ)).inverseImage.obj
        (presentationInverseImage φ F) ≅
      (smallEtaleMorphismOfTopoi (relationS φ)).inverseImage.obj
        (presentationInverseImage φ F) :=
  ((smallEtaleMorphismOfTopoiComp (relationT φ) φ).app F).symm ≪≫
    eqToIso (congrArg (fun f ↦ (smallEtaleMorphismOfTopoi f).inverseImage.obj F)
      (pullback.condition : relationT φ ≫ φ = relationS φ ≫ φ)) ≪≫
    (smallEtaleMorphismOfTopoiComp (relationS φ) φ).app F

/-- `presentationInverseImageIso φ F` is the composite of the two
`smallEtaleMorphismOfTopoiComp` comparisons along `t ≫ φ = s ≫ φ`. -/
theorem presentationInverseImageIso_spec (φ : ofOver U ⟶ X)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    presentationInverseImageIso φ F =
      ((smallEtaleMorphismOfTopoiComp (relationT φ) φ).app F).symm ≪≫
        eqToIso (congrArg (fun f ↦ (smallEtaleMorphismOfTopoi f).inverseImage.obj F)
          (pullback.condition : relationT φ ≫ φ = relationS φ ≫ φ)) ≪≫
        (smallEtaleMorphismOfTopoiComp (relationS φ) φ).app F :=
  sorry

/-- Whiskering `α` along a morphism into the kernel pair, producing
`(f ≫ t)^{-1} G ≅ (f ≫ s)^{-1} G`. -/
def presentationInverseImageIso_comp (φ : ofOver U ⟶ X)
    {V : AlgebraicSpace S} (f : V ⟶ pullback φ φ)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (smallEtaleMorphismOfTopoi (f ≫ relationT φ)).inverseImage.obj
        (presentationInverseImage φ F) ≅
      (smallEtaleMorphismOfTopoi (f ≫ relationS φ)).inverseImage.obj
        (presentationInverseImage φ F) :=
  (smallEtaleMorphismOfTopoiComp f (relationT φ)).app (presentationInverseImage φ F) ≪≫
    (smallEtaleMorphismOfTopoi f).inverseImage.mapIso (presentationInverseImageIso φ F) ≪≫
    ((smallEtaleMorphismOfTopoiComp f (relationS φ)).app (presentationInverseImage φ F)).symm

/-- The inverse-image isos `pr0^{-1} α`, `pr1^{-1} α`, and `c^{-1} α` satisfy the
cocycle identity after functoriality identifications. -/
theorem presentationInverseImageIso_cocycle (φ : ofOver U ⟶ X)
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    presentationInverseImageIso_comp φ (relationC φ) F =
      eqToIso
          (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage.obj
            (presentationInverseImage φ F))
            (relationC_comp_relationT φ)) ≪≫
        presentationInverseImageIso_comp φ (relationPr0 φ) F ≪≫
        eqToIso
          (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage.obj
            (presentationInverseImage φ F))
            (pullback.condition :
              relationPr0 φ ≫ relationS φ = relationPr1 φ ≫ relationT φ)) ≪≫
        presentationInverseImageIso_comp φ (relationPr1 φ) F ≪≫
        eqToIso
          (congrArg (fun h ↦ (smallEtaleMorphismOfTopoi h).inverseImage.obj
            (presentationInverseImage φ F))
            (relationC_comp_relationS φ).symm) :=
  sorry

/-- Descent data for small étale sheaves of types along the singleton atlas covering
`{U ⟶ X}` in `X_spaces,étale`. -/
abbrev presentationDescent (φ : ofOver U ⟶ X) [Etale φ] :=
  ((spacesEtaleTopology X).pseudofunctorOver (Type (u + 1))).DescentData
    (fun _ : PUnit ↦ atlasToSelf φ)

/-- The functor sending a small étale sheaf on `X` to its descent datum
`(G, α)` along an étale atlas. -/
def sheafToPresentationDescent (φ : ofOver U ⟶ X) [Etale φ] :
    Sheaf (smallEtaleTopology X) (Type (u + 1)) ⥤ presentationDescent φ :=
  smallEtaleInclusionDirectImage X ⋙
    (spacesEtaleTopology X).overPullback (Type (u + 1)) (spacesEtaleSite.self X) ⋙
      ((spacesEtaleTopology X).pseudofunctorOver (Type (u + 1))).toDescentData
        (fun _ : PUnit ↦ atlasToSelf φ)

/-- The object map of `sheafToPresentationDescent φ` is restriction to the slice
over the terminal object, followed by `toDescentData` of the atlas covering. -/
theorem sheafToPresentationDescent_obj (φ : ofOver U ⟶ X) [Etale φ]
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    (sheafToPresentationDescent φ).obj F =
      (((spacesEtaleTopology X).pseudofunctorOver (Type (u + 1))).toDescentData
          (fun _ : PUnit ↦ atlasToSelf φ)).obj
        (((spacesEtaleTopology X).overPullback (Type (u + 1))
            (spacesEtaleSite.self X)).obj
          ((smallEtaleInclusionDirectImage X).obj F)) :=
  sorry

/-- For a surjective étale atlas, small étale sheaves on `X` are equivalent to
descent data along `{U ⟶ X}`. -/
theorem sheafToPresentationDescent_isEquivalence (φ : ofOver U ⟶ X) [Etale φ]
    (h_surj : Function.Surjective (Points.map φ)) :
    (sheafToPresentationDescent φ).IsEquivalence :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
