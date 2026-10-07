module

public import ReasLib.AlgebraicGeometry.RingedSite.CommRing
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ringed

/-!
# Commutative small étale ringed morphisms

The morphism of commutative ringed-site presentations associated to a scheme morphism is the
small-étale base-change functor together with the universe-lifted global-sections maps of the
fibre-product projections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open Scheme.AssociatedModule

noncomputable section

universe u

namespace Scheme.Etale.Small

variable {X Y : Scheme.{u}}

/-- Continuous small étale base change is a morphism of the lifted commutative small étale
sites. -/
instance commRingedHom_base_isMorphismOfSites (f : X ⟶ Y) :
    IsMorphismOfSites
      (smallCommRingedSite .etale Y).siteTopology
      (smallCommRingedSite .etale X).siteTopology
      (Scheme.smallEtalePullback f) :=
  sorry

/-- Small étale base change is continuous for the lifted commutative small étale topologies. -/
instance commRingedHom_base_isContinuous (f : X ⟶ Y) :
    (Scheme.smallEtalePullback f).IsContinuous
      (smallCommRingedSite .etale Y).siteTopology
      (smallCommRingedSite .etale X).siteTopology :=
  (commRingedHom_base_isMorphismOfSites f).toIsContinuous

/-- Continuous small étale base change is a right adjoint on commutative-ring sheaves. -/
instance smallEtalePullback_sheafPushforwardContinuous_commRing_isRightAdjoint
    (f : X ⟶ Y) :
    ((Scheme.smallEtalePullback f).sheafPushforwardContinuous CommRingCat.{u + 1}
      (smallCommRingedSite .etale Y).siteTopology
      (smallCommRingedSite .etale X).siteTopology).IsRightAdjoint :=
  sorry

/-- The universe-lifted commutative global-sections map induced by small étale base change. -/
noncomputable def commStructurePresheafMap (f : X ⟶ Y) :
    (StandardSmall.commStructureSheaf .etale Y).obj ⟶
      (Scheme.smallEtalePullback f).op ⋙
        (StandardSmall.commStructureSheaf .etale X).obj where
  app U :=
    (CommRingCat.universeLift.{u, u + 1}).map
      (CommRingCat.ofHom (pullback.fst U.unop.hom f).appTop.hom)
  naturality _ _ _ := sorry

/-- At an étale object of `Y`, `commStructurePresheafMap f` is the universe lift of the
global-sections map of the fibre-product projection. -/
theorem commStructurePresheafMap_app (f : X ⟶ Y) (U : Y.Etaleᵒᵖ) :
    (commStructurePresheafMap f).app U =
      (CommRingCat.universeLift.{u, u + 1}).map
        (CommRingCat.ofHom (pullback.fst U.unop.hom f).appTop.hom) :=
  sorry

/-- The sheaf morphism of lifted commutative structure sheaves associated to `f`. -/
noncomputable def commStructureSheafMap (f : X ⟶ Y) :
    StandardSmall.commStructureSheaf .etale Y ⟶
      ((Scheme.smallEtalePullback f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (smallCommRingedSite .etale Y).siteTopology
        (smallCommRingedSite .etale X).siteTopology).obj
        (StandardSmall.commStructureSheaf .etale X) :=
  ⟨commStructurePresheafMap f⟩

/-- A scheme morphism induces a morphism of small étale commutative ringed sites. -/
noncomputable def commRingedHom (f : X ⟶ Y) :
    RingedSite.Hom (smallCommRingedSite .etale X)
      (smallCommRingedSite .etale Y) where
  base := Scheme.smallEtalePullback f
  isMorphismOfSites := commRingedHom_base_isMorphismOfSites f
  structureSheafMap :=
    (sheafCompose
      (smallCommRingedSite .etale Y).siteTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (commStructureSheafMap f)

/-- The base of the commutative small-étale ringed morphism is small-étale base change. -/
theorem commRingedHom_base (f : X ⟶ Y) :
    (commRingedHom f).base = Scheme.smallEtalePullback f :=
  sorry

/-- The structure-map component of the commutative small-étale ringed morphism is the
universe-lifted fibre-product projection on global sections. -/
theorem commRingedHom_structureSheafMap_app (f : X ⟶ Y) (U : Y.Etaleᵒᵖ) :
    (commRingedHom f).structureSheafMap.hom.app U =
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}).map
        ((CommRingCat.universeLift.{u, u + 1}).map
          (CommRingCat.ofHom (pullback.fst U.unop.hom f).appTop.hom)) :=
  sorry

end Scheme.Etale.Small
