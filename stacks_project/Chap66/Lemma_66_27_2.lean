module

public import stacks_project.Chap66.Lemma_66_27_2_Parameter
public import stacks_project.Chap66.Lemma_66_27_2_LocalizationAt
public import stacks_project.Chap66.Lemma_66_27_2_Comparison
public import stacks_project.Chap66.Lemma_66_27_2_SchemeBridge
public import stacks_project.Chap66.Lemma_66_27_2_Slice
public import stacks_project.Chap66.Lemma_66_27_2_Ambient
public import stacks_project.Chap66.Lemma_66_27_2_ParameterBridge
public import stacks_project.Chap66.Lemma_66_27_2_Endpoint

/-! # Relocalization of small-étale ringed topoi at schemes

The comparison starts at the actual conjugate of `g_small` and ends at the
18.22.3 inverse-image formula for the actual sheaf parameter `s`.
The previous spaces comparison is retained as the middle factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {U V : Over S} {X Y : AlgebraicSpace S}
variable (p : ofOver U ⟶ X) (g : ofOver U ⟶ ofOver V) (f : X ⟶ Y) (q : ofOver V ⟶ Y)
variable [Etale p] [Etale q]

/-- The three actual direct-image comparisons: scheme identification, the retained
spaces comparison, and transport to the specified parameter inverse image. -/
def etaleRelocalizeIso_homIso (hcomm : p ≫ f = g ≫ q) :
    (etaleRelocalizeConjugateScheme p g q).toTopos.pushforward ≅
      (Relocalization.parameterRingedHom p g f q hcomm).toTopos.pushforward :=
  (Relocalization.conjugateSchemeTwoIso p g f q hcomm).homIso ≪≫
    (etaleRelocalizeViaSpacesIso p g f q hcomm).homIso ≪≫
      (Relocalization.parameterTwoIso p g f q hcomm).homIso

/-- Lemma 66.27.2: via (66.27.0.4), the actual `(g_small, g^♯)` is 2-isomorphic
to the 18.22.3 localization of `(f_small, f^♯)` at the sheaf map
`s : h_U ⟶ f_small⁻¹ h_V` corresponding to the given arbitrary commutative square. -/
@[stacks 04M5]
def etaleRelocalizeIso (hcomm : p ≫ f = g ≫ q) :
    @RingedSite.ToposHom.TwoIso
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (etaleRelocalizeConjugateScheme p g q)
      (Relocalization.parameterRingedHom p g f q hcomm) where
  homIso := etaleRelocalizeIso_homIso p g f q hcomm
  comm := (((Relocalization.conjugateSchemeTwoIso p g f q hcomm).hom.comp
    (etaleRelocalizeViaSpacesIso p g f q hcomm).hom).comp
      (Relocalization.parameterTwoIso p g f q hcomm).hom).comm

/-- On every source-slice sheaf, the actual comparison is the three-factor pasting. -/
theorem etaleRelocalizeIso_homIso_app (hcomm : p ≫ f = g ≫ q)
    (F : Sheaf ((smallEtaleTopology X).over (smallEtaleSite.mk p)) (Type u)) :
    (etaleRelocalizeIso p g f q hcomm).homIso.hom.app F =
      (Relocalization.conjugateSchemeTwoIso p g f q hcomm).homIso.hom.app F ≫
        (etaleRelocalizeViaSpacesIso p g f q hcomm).homIso.hom.app F ≫
          (Relocalization.parameterTwoIso p g f q hcomm).homIso.hom.app F := rfl

/-- The source-faithful comparison as a morphism of ringed topoi. -/
def etaleRelocalizeIso_hom (hcomm : p ≫ f = g ≫ q) :
    @RingedSite.ToposHom.TwoMorphism
      ((ringedSite X).localization (smallEtaleSite.mk p))
      ((ringedSite Y).localization (smallEtaleSite.mk q)) _ _
      (etaleRelocalizeConjugateScheme p g q)
      (Relocalization.parameterRingedHom p g f q hcomm) :=
  (etaleRelocalizeIso p g f q hcomm).hom

/-- The comparison is invertible on its direct-image natural transformation. -/
instance etaleRelocalizeIso_homIso_isIso (hcomm : p ≫ f = g ≫ q) :
    IsIso (etaleRelocalizeIso p g f q hcomm).homIso.hom := inferInstance

end AlgebraicGeometry.AlgebraicSpace
