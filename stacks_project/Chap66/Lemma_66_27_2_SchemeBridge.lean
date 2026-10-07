module

public import stacks_project.Chap66.Lemma_66_27_2_Comparison

/-! # Concrete small/spaces comparison for the scheme conjugate -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace CategoryTheory.Equivalence

/-- Transfer a commuting square across specified equivalences, using their unit and counit. -/
def transferSquare.{uA, uB, uC, uD} {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [Category A] [Category B] [Category C] [Category D]
    (E : A ≌ B) (F : C ≌ D) (H : B ⥤ D) (K : A ⥤ C)
    (e : K ⋙ F.functor ≅ E.functor ⋙ H) :
    H ⋙ F.inverse ≅ E.inverse ⋙ K :=
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight E.counitIso.symm (H ⋙ F.inverse) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft E.inverse
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight e.symm F.inverse ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft K F.unitIso.symm ≪≫ Functor.rightUnitor K)

end CategoryTheory.Equivalence

namespace AlgebraicGeometry.AlgebraicSpace.Relocalization

variable {S : Scheme.{u}}

/-- Small charts form a dense subsite also for Type-u sheaves. -/
instance restriction_isEquivalence (X : AlgebraicSpace S) :
    ((smallEtaleInclusion X).sheafPushforwardContinuous (Type u)
      (smallEtaleTopology X) (spacesEtaleTopology X)).IsEquivalence := sorry

/-- The comparison uses exactly the existing restriction/right-Kan-extension adjunction. -/
def inclusionEquivalence (X : AlgebraicSpace S) :
    Sheaf (spacesEtaleTopology X) (Type u) ≌ Sheaf (smallEtaleTopology X) (Type u) :=
  ((smallEtaleInclusion X).sheafAdjunctionCocontinuous (Type u)
    (smallEtaleTopology X) (spacesEtaleTopology X)).toEquivalence

variable {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X) [Etale p]

/-- The image of a scheme slice object, rebased to the ordinary spaces-site object. -/
def sliceInclusion : Over (smallEtaleSite.mk p) ⥤ Over (spacesEtaleSite.mk p) :=
  smallEtaleOverPost X (smallEtaleSite.mk p) ⋙ Over.map (smallEtaleInclusion_mkIso p).hom

/-- Postcomposition to the slice commutes with passage from schemes to spaces.
Each component is identity on the represented scheme. -/
def localizationSquare :
    etaleLocalizationFunctor p ⋙ sliceInclusion p ≅
      smallEtaleInclusion (ofOver U) ⋙ spacesEtaleLocalizationFunctor p :=
  NatIso.ofComponents
    (fun W ↦ Over.isoMk (MorphismProperty.Over.isoMk (Iso.refl _) sorry) sorry) sorry

/-- Forgetting a scheme slice arrow commutes with passage to spaces.
Each component is identity on the underlying algebraic space. -/
def localizationInverseSquare :
    etaleLocalizationInverse p ⋙ smallEtaleInclusion (ofOver U) ≅
      sliceInclusion p ⋙ spacesEtaleLocalizationInverse p :=
  NatIso.ofComponents
    (fun W ↦ MorphismProperty.Over.isoMk (Iso.refl _) sorry) sorry

/-- Restriction along a slice isomorphism is an equivalence of sheaf categories. -/
instance overIsoRestriction_isEquivalence {Z : AlgebraicSpace S}
    {A B : spacesEtaleSite Z} (e : A ≅ B) :
    ((Over.map e.hom).sheafPushforwardContinuous (Type u)
      ((spacesEtaleTopology Z).over A) ((spacesEtaleTopology Z).over B)).IsEquivalence := sorry

/-- The composite slice inclusion is continuous. -/
instance sliceInclusion_isContinuous :
    (sliceInclusion p).IsContinuous ((smallEtaleTopology X).over (smallEtaleSite.mk p))
      ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) :=
  Functor.isContinuous_comp (smallEtaleOverPost X (smallEtaleSite.mk p))
    (Over.map (smallEtaleInclusion_mkIso p).hom)
    ((smallEtaleTopology X).over (smallEtaleSite.mk p))
    ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)))
    ((spacesEtaleTopology X).over (spacesEtaleSite.mk p))

/-- Continuity of the upper path of the localization square. -/
instance localizationSquare_left_isContinuous :
    (etaleLocalizationFunctor p ⋙ sliceInclusion p).IsContinuous
      (smallEtaleTopology (ofOver U)) ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) :=
  Functor.isContinuous_comp (etaleLocalizationFunctor p) (sliceInclusion p)
    (smallEtaleTopology (ofOver U)) ((smallEtaleTopology X).over (smallEtaleSite.mk p))
    ((spacesEtaleTopology X).over (spacesEtaleSite.mk p))

/-- The source slice equivalence with inverse exactly the extension used in the old comparison. -/
def sliceEquivalence :
    Sheaf ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) (Type u) ≌
      Sheaf ((smallEtaleTopology X).over (smallEtaleSite.mk p)) (Type u) :=
  (((Over.map (smallEtaleInclusion_mkIso p).hom).sheafAdjunctionCocontinuous (Type u)
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj (smallEtaleSite.mk p)))
      ((spacesEtaleTopology X).over (spacesEtaleSite.mk p))).comp
    ((smallEtaleOverPost X (smallEtaleSite.mk p)).sheafAdjunctionCocontinuous (Type u)
      ((smallEtaleTopology X).over (smallEtaleSite.mk p))
      ((spacesEtaleTopology X).over ((smallEtaleInclusion X).obj (smallEtaleSite.mk p))))).toEquivalence

/-- The restriction square induced by the identity-on-space localization square. -/
def restrictionSquare :
    (spacesEtaleLocalizationFunctor p).sheafPushforwardContinuous (Type u)
        (spacesEtaleTopology (ofOver U)) ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) ⋙
      (inclusionEquivalence (ofOver U)).functor ≅
    (sliceEquivalence p).functor ⋙
      (etaleLocalizationFunctor p).sheafPushforwardContinuous (Type u)
        (smallEtaleTopology (ofOver U)) ((smallEtaleTopology X).over (smallEtaleSite.mk p)) :=
  (Functor.sheafPushforwardContinuousComp'
    (localizationSquare p).symm (Type u) (smallEtaleTopology (ofOver U))
      (spacesEtaleTopology (ofOver U)) ((spacesEtaleTopology X).over (spacesEtaleSite.mk p))) ≪≫
    (Functor.sheafPushforwardContinuousComp _ _ (Type u)
      (smallEtaleTopology (ofOver U)) ((smallEtaleTopology X).over (smallEtaleSite.mk p))
      ((spacesEtaleTopology X).over (spacesEtaleSite.mk p))).symm

/-- Source localization commutes with small-to-spaces extension by the canonical mate. -/
def sourceIso :
    (etaleLocalizationIso_inv_toToposHom p).toTopos.pushforward ⋙
        (inclusionEquivalence (ofOver U)).inverse ≅
      (sliceEquivalence p).inverse ⋙
        (spacesEtaleLocalizationIso_inv_toToposHom p).toTopos.pushforward :=
  (sliceEquivalence p).transferSquare (inclusionEquivalence (ofOver U)) _ _ (restrictionSquare p)

/-- The forward functor of the slice equivalence is the cocontinuous postcomposition. -/
instance overIso_functor_isCocontinuous {Z : AlgebraicSpace S}
    {A B : spacesEtaleSite Z} (e : A ≅ B) :
    (Over.mapIso e).functor.IsCocontinuous
      ((spacesEtaleTopology Z).over A) ((spacesEtaleTopology Z).over B) :=
  inferInstanceAs ((Over.map e.hom).IsCocontinuous _ _)

/-- The inverse functor of the slice equivalence is cocontinuous postcomposition. -/
instance overIso_inverse_isCocontinuous {Z : AlgebraicSpace S}
    {A B : spacesEtaleSite Z} (e : A ≅ B) :
    (Over.mapIso e).inverse.IsCocontinuous
      ((spacesEtaleTopology Z).over B) ((spacesEtaleTopology Z).over A) :=
  inferInstanceAs ((Over.map e.inv).IsCocontinuous _ _)

/-- A slice isomorphism identifies the slice topologies in either direction. -/
instance overIso_inverse_dense {Z : AlgebraicSpace S} {A B : spacesEtaleSite Z} (e : A ≅ B) :
    (Over.mapIso e).inverse.IsDenseSubsite
      ((spacesEtaleTopology Z).over B) ((spacesEtaleTopology Z).over A) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ (Over.mapIso e)

/-- Restriction along an isomorphism is the specified right adjoint to restriction
along its inverse, hence identifies with the existing right-Kan extension. -/
def overIsoPushforward {Z : AlgebraicSpace S} {A B : spacesEtaleSite Z} (e : A ≅ B) :
    (Over.map e.hom).sheafPushforwardContinuous (Type u)
        ((spacesEtaleTopology Z).over A) ((spacesEtaleTopology Z).over B) ≅
      (Over.map e.inv).sheafPushforwardCocontinuous (Type u)
        ((spacesEtaleTopology Z).over B) ((spacesEtaleTopology Z).over A) :=
  Adjunction.rightAdjointUniq
    ((Over.mapIso e).sheafCongr ((spacesEtaleTopology Z).over A)
      ((spacesEtaleTopology Z).over B) (Type u)).toAdjunction
    ((Over.map e.inv).sheafAdjunctionCocontinuous (Type u)
      ((spacesEtaleTopology Z).over B) ((spacesEtaleTopology Z).over A))

/-- Continuity of the spaces path in the inverse localization square. -/
instance inverseSquare_right_isContinuous :
    (sliceInclusion p ⋙ spacesEtaleLocalizationInverse p).IsContinuous
      ((smallEtaleTopology X).over (smallEtaleSite.mk p)) (spacesEtaleTopology (ofOver U)) :=
  Functor.isContinuous_comp (sliceInclusion p) (spacesEtaleLocalizationInverse p)
    ((smallEtaleTopology X).over (smallEtaleSite.mk p))
    ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) (spacesEtaleTopology (ofOver U))

/-- Target localization commutes with spaces-to-small restriction and the mk-object rebase. -/
def targetIso :
    (inclusionEquivalence (ofOver U)).functor ⋙
        (etaleLocalizationIso_hom_toToposHom p).toTopos.pushforward ≅
      (spacesEtaleLocalizationIso_hom_toToposHom p).toTopos.pushforward ⋙
        (etaleRelocalizeMkRelocalization_target p).toTopos.pushforward ⋙
          (smallEtaleLocalizationComparisonInv X (smallEtaleSite.mk p)).toTopos.pushforward :=
  Functor.sheafPushforwardContinuousComp' (localizationInverseSquare p) (Type u)
      ((smallEtaleTopology X).over (smallEtaleSite.mk p)) (smallEtaleTopology (ofOver U))
      (spacesEtaleTopology (ofOver U)) ≪≫
    (Functor.sheafPushforwardContinuousComp (sliceInclusion p) (spacesEtaleLocalizationInverse p)
      (Type u) ((smallEtaleTopology X).over (smallEtaleSite.mk p))
      ((spacesEtaleTopology X).over (spacesEtaleSite.mk p)) (spacesEtaleTopology (ofOver U))).symm ≪≫
    Functor.isoWhiskerLeft (spacesEtaleLocalizationIso_hom_toToposHom p).toTopos.pushforward
      (Functor.isoWhiskerRight (overIsoPushforward (smallEtaleInclusion_mkIso p))
        (smallEtaleLocalizationComparisonInv X (smallEtaleSite.mk p)).toTopos.pushforward)

/-- The direct-image comparison for an arbitrary morphism, before localization.
It is induced by the actual base-change square of site functors. -/
def morphismPushforwardIso {Z W : AlgebraicSpace S} (g : Z ⟶ W) :
    (ringedToposHom g).toTopos.pushforward ≅
      (inclusionEquivalence Z).inverse ⋙
        (spacesRingedToposHom g).toTopos.pushforward ⋙
          (inclusionEquivalence W).functor :=
  Functor.isoWhiskerLeft (inclusionEquivalence Z).inverse
    (Functor.sheafPushforwardContinuousComp'
      (smallEtaleInclusion_comp_spacesEtalePullback g) (Type u)
      (smallEtaleTopology W) (spacesEtaleTopology W) (spacesEtaleTopology Z)).symm

variable {V : Over S} {Y : AlgebraicSpace S}
variable (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y) [Etale q]

/-- The actual scheme conjugate is compared with the old spaces-route conjugate
by the source mate, base-change square, and target restriction square. -/
def conjugateSchemeIso (hcomm : p ≫ f = g ≫ q) :
    (etaleRelocalizeConjugateScheme p g q).toTopos.pushforward ≅
      (etaleRelocalizeConjugate p g f q hcomm).toTopos.pushforward :=
  Functor.isoWhiskerLeft (etaleLocalizationIso_inv_toToposHom p).toTopos.pushforward
      (Functor.isoWhiskerRight (morphismPushforwardIso g)
        (etaleLocalizationIso_hom_toToposHom q).toTopos.pushforward) ≪≫
    Functor.isoWhiskerRight (sourceIso p)
      ((spacesRingedToposHom g).toTopos.pushforward ⋙
        (inclusionEquivalence (ofOver V)).functor ⋙
          (etaleLocalizationIso_hom_toToposHom q).toTopos.pushforward) ≪≫
    Functor.isoWhiskerLeft (sliceEquivalence p).inverse
      (Functor.isoWhiskerLeft (spacesEtaleLocalizationIso_inv_toToposHom p).toTopos.pushforward
        (Functor.isoWhiskerLeft (spacesRingedToposHom g).toTopos.pushforward (targetIso q)))

/-- Ringed version of the explicit scheme/spaces comparison. Its compatibility
is the naturality of the structure-sheaf restriction and extension maps. -/
def conjugateSchemeTwoIso (hcomm : p ≫ f = g ≫ q) :
    @RingedSite.ToposHom.TwoIso
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (etaleRelocalizeConjugateScheme p g q)
      (etaleRelocalizeConjugate p g f q hcomm) where
  homIso := conjugateSchemeIso p g f q hcomm
  comm := sorry

end AlgebraicGeometry.AlgebraicSpace.Relocalization
