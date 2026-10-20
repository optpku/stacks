/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Deformation.Presentation
import StacksCheckRecall

/-! # Versal cogroupoid presentations -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite IsLocalRing
open AlgebraicGeometry.AlgebraicStack (FieldValuedPoint)
open FiberedCategoryOver.Groupoids
open CompleteLocalAlgCat
open GroupoidInFunctors
open scoped Bicategory BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
  [AlgebraicStack X]
  [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
  (x0 : FieldValuedPoint X)
  [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
  {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Algebra Λ x0.K]
  [Module.Finite Λ x0.K]
  (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
  [IsOpenImmersion openImmersion]
  (h_factor :
    Spec.map (CommRingCat.ofHom (algebraMap Λ x0.K)) ≫ openImmersion =
      x0.structureHom)

/- Remark 107.2.11. A compatible versal cogroupoid presents the deformation category
and its completion, and its object algebra is a versal ring. -/
@[stacks 0DR3] #check (AlgebraicGeometry.GroupoidsOver.Predeformation.exists_versalCogroupoidPresentation x0 openImmersion h_factor :
    (∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ x0.K))
      (φ : G.quotient ⟶ bundled openImmersion x0.structureHom h_factor X x0.fiberObj),
      GroupoidInFunctors.IsSmooth G.s G.t ∧ GroupoidInFunctors.IsProrepresentable G ∧
        GroupoidInFunctors.IsPresentation G
          (bundled openImmersion x0.structureHom h_factor X x0.fiberObj) φ) ∧
    ∃ (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
      (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B)
      (e : restrictedCoyoneda B ≅ relation (_root_.FormalObject.associatedMorphismOver ξ))
      (c : B ⟶ pushout s t)
      (idMap : coyoneda.obj (op ξ.base) ⟶ coyoneda.obj (op B))
      (invMap : coyoneda.obj (op B) ⟶ coyoneda.obj (op B))
      (laws : CoyonedaGroupoidLaws s t c idMap invMap)
      (ε : GroupoidInFunctors.Iso
        (restrictInclusion (ofCoyoneda s t c idMap invMap laws)) (ofFormalObject ξ)),
      _root_.FormalObject.IsVersal ξ ∧
      e.hom ≫ src (_root_.FormalObject.associatedMorphismOver ξ) = restrictedCoyonedaMap s ∧
      e.hom ≫ tgt (_root_.FormalObject.associatedMorphismOver ξ) = restrictedCoyonedaMap t ∧
      IsPowerSeriesOver s ∧ IsPowerSeriesOver t ∧
      ε.hom.obj = 𝟙 _ ∧ ε.hom.arrow = e.hom ∧
      BasedFunctor.IsEquivalence (quotientMap (_root_.FormalObject.associatedMorphismOver ξ)) ∧
      BasedFunctor.IsEquivalence (coyonedaQuotientMap ξ ε) ∧
      AlgebraicStack.IsVersalRing x0 (toSAlgebra x0 openImmersion h_factor ξ))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.exists_smoothProrepresentablePresentation x0 openImmersion h_factor :
    ∃ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ x0.K))
      (φ : G.quotient ⟶ bundled openImmersion x0.structureHom h_factor X x0.fiberObj),
      GroupoidInFunctors.IsSmooth G.s G.t ∧ GroupoidInFunctors.IsProrepresentable G ∧
        GroupoidInFunctors.IsPresentation G (bundled openImmersion x0.structureHom h_factor X x0.fiberObj) φ)

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.exists_versalFormalObject x0 openImmersion h_factor :
    ∃ ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor),
      _root_.FormalObject.IsVersal ξ)

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.exists_kernelPairAlgebra x0 openImmersion h_factor :
    ∀ (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ],
    ∃ (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B)
      (e : restrictedCoyoneda B ≅
        relation (_root_.FormalObject.associatedMorphismOver ξ)),
      e.hom ≫ src (_root_.FormalObject.associatedMorphismOver ξ) =
          restrictedCoyonedaMap s ∧
        e.hom ≫ tgt (_root_.FormalObject.associatedMorphismOver ξ) =
          restrictedCoyonedaMap t ∧
        IsPowerSeriesOver s ∧ IsPowerSeriesOver t)

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.exists_cogroupoidComp x0 openImmersion h_factor :
    ∀ (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ]
    (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B)
    (e : restrictedCoyoneda B ≅ relation (_root_.FormalObject.associatedMorphismOver ξ)),
    (e.hom ≫ src (_root_.FormalObject.associatedMorphismOver ξ) = restrictedCoyonedaMap s) →
    (e.hom ≫ tgt (_root_.FormalObject.associatedMorphismOver ξ) = restrictedCoyonedaMap t) →
    IsPowerSeriesOver s → IsPowerSeriesOver t →
    ∃ (c : B ⟶ pushout s t)
      (idMap : coyoneda.obj (op ξ.base) ⟶ coyoneda.obj (op B))
      (invMap : coyoneda.obj (op B) ⟶ coyoneda.obj (op B))
      (laws : CoyonedaGroupoidLaws s t c idMap invMap)
      (ε : GroupoidInFunctors.Iso
        (restrictInclusion (ofCoyoneda s t c idMap invMap laws))
        (ofFormalObject ξ)),
      ε.hom.obj = 𝟙 _ ∧ ε.hom.arrow = e.hom)

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.isPresentation_restrict x0 openImmersion h_factor :
    ∀ (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ],
    BasedFunctor.IsEquivalence
      (quotientMap (_root_.FormalObject.associatedMorphismOver ξ)))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.isPresentation_completion x0 openImmersion h_factor :
    ∀ (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ]
    (B : CompleteLocalAlgCat Λ x0.K) (s t : ξ.base ⟶ B)
    (c : B ⟶ pushout s t)
    (idMap : coyoneda.obj (op ξ.base) ⟶ coyoneda.obj (op B))
    (invMap : coyoneda.obj (op B) ⟶ coyoneda.obj (op B))
    (laws : CoyonedaGroupoidLaws s t c idMap invMap)
    (e : GroupoidInFunctors.Iso
      (restrictInclusion (ofCoyoneda s t c idMap invMap laws)) (ofFormalObject ξ)),
    BasedFunctor.IsEquivalence (coyonedaQuotientMap ξ e))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.instIsVersalRing_toSAlgebra x0 openImmersion h_factor :
    ∀ (ξ : _root_.FormalObject (predeformationLiftProjection x0 openImmersion h_factor))
    [_root_.FormalObject.IsVersal ξ],
    AlgebraicStack.IsVersalRing x0 (toSAlgebra x0 openImmersion h_factor ξ))

end AlgebraicGeometry.GroupoidsOver.Predeformation
