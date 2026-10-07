module

public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction

/-!
# Commutative presentations of ε and of small Zariski morphisms

The morphism ε of 75.4.0.1 and the small Zariski morphism induced by a scheme
morphism are packaged here as morphisms of lifted commutative small ringed
sites, so that inverse-image structure sheaves and relative Tor-amplitude are
available.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

variable {X Y : Scheme.{u}}

/-- The inclusion of open immersions among étale morphisms is a morphism of the
lifted commutative small sites. -/
instance commSmallEtaleToZariski_base_isMorphismOfSites (S : Scheme.{u}) :
    IsMorphismOfSites
      (smallCommRingedSite .zariski S).siteTopology
      (smallCommRingedSite .etale S).siteTopology
      (smallZariskiToSmallEtale S) := sorry

/-- Small Zariski base change is a morphism of the lifted commutative small
Zariski sites. -/
instance zariskiCommRingedHom_base_isMorphismOfSites (f : X ⟶ Y) :
    IsMorphismOfSites
      (smallCommRingedSite .zariski Y).siteTopology
      (smallCommRingedSite .zariski X).siteTopology
      (smallZariskiPullback f) := sorry

/-- The Zariski-to-étale inclusion is continuous on packaged small commutative
sites. -/
instance commSmallEtaleToZariski_base_isContinuous_site (S : Scheme.{u}) :
    (smallZariskiToSmallEtale S).IsContinuous
      (smallCommRingedSite .zariski S).siteTopology
      (smallCommRingedSite .etale S).siteTopology :=
  (commSmallEtaleToZariski_base_isMorphismOfSites S).toIsContinuous

/-- Small Zariski base change is continuous on packaged small commutative
Zariski sites. -/
instance zariskiCommRingedHom_base_isContinuous_site (f : X ⟶ Y) :
    (smallZariskiPullback f).IsContinuous
      (smallCommRingedSite .zariski Y).siteTopology
      (smallCommRingedSite .zariski X).siteTopology :=
  (zariskiCommRingedHom_base_isMorphismOfSites f).toIsContinuous

/-- The Zariski-to-étale inclusion is continuous on unfolded small standard
topologies. -/
instance commSmallEtaleToZariski_base_isContinuous (S : Scheme.{u}) :
    (smallZariskiToSmallEtale S).IsContinuous
      (StandardTopology.Small.topology .zariski S)
      (StandardTopology.Small.topology .etale S) := sorry

/-- Small Zariski base change is continuous on unfolded small standard Zariski
topologies. -/
instance zariskiCommRingedHom_base_isContinuous (f : X ⟶ Y) :
    (smallZariskiPullback f).IsContinuous
      (StandardTopology.Small.topology .zariski Y)
      (StandardTopology.Small.topology .zariski X) := sorry

/-- The structure-sheaf component of the commutative small Zariski-to-étale
restriction. -/
noncomputable def commSmallEtaleToZariskiStructureSheafMap (S : Scheme.{u}) :
    StandardSmall.commStructureSheaf .zariski S ⟶
      ((smallZariskiToSmallEtale S).sheafPushforwardContinuous CommRingCat.{u + 1}
        (StandardTopology.Small.topology .zariski S)
        (StandardTopology.Small.topology .etale S)).obj
        (StandardSmall.commStructureSheaf .etale S) where
  hom :=
    { app := fun U ↦
        (CommRingCat.universeLift.{u, u + 1}).map
          (Scheme.Γ.map
            (𝟙 ((Scheme.smallZariskiToScheme S).obj U.unop)).op)
      naturality := sorry }

/-- At a small Zariski object, `commSmallEtaleToZariskiStructureSheafMap` is the
universe lift of the identity on global sections. -/
theorem commSmallEtaleToZariskiStructureSheafMap_app
    (S : Scheme.{u}) (U) :
    (commSmallEtaleToZariskiStructureSheafMap S).hom.app U =
      (CommRingCat.universeLift.{u, u + 1}).map
        (Scheme.Γ.map
          (𝟙 ((Scheme.smallZariskiToScheme S).obj U.unop)).op) := sorry

/-- The commutative-ring presentation of ε from 75.4.0.1, as a morphism of
lifted small ringed sites `(X_étale, 𝒪_étale) ⟶ (X_Zar, 𝒪_X)`. -/
noncomputable def commSmallEtaleToZariski (S : Scheme.{u}) :
    RingedSite.Hom
      (smallCommRingedSite .etale S) (smallCommRingedSite .zariski S) where
  base := smallZariskiToSmallEtale S
  isMorphismOfSites := commSmallEtaleToZariski_base_isMorphismOfSites S
  structureSheafMap :=
    (sheafCompose (smallCommRingedSite .zariski S).siteTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (commSmallEtaleToZariskiStructureSheafMap S)

/-- The base of `commSmallEtaleToZariski` is the inclusion of open immersions among
étale morphisms. -/
theorem commSmallEtaleToZariski_base (S : Scheme.{u}) :
    (commSmallEtaleToZariski S).base = smallZariskiToSmallEtale S := sorry

/-- Continuous pushforward of commutative-ring sheaves along
`commSmallEtaleToZariski` is a right adjoint on unfolded small standard
topologies. -/
instance (priority := high) commSmallEtaleToZariski_sheafPushforwardContinuous_isRightAdjoint
    (S : Scheme.{u}) :
    ((commSmallEtaleToZariski S).base.sheafPushforwardContinuous CommRingCat.{u + 1}
      (StandardTopology.Small.topology .zariski S)
      (StandardTopology.Small.topology .etale S)).IsRightAdjoint := sorry

/-- Continuous pushforward of commutative-ring sheaves along
`commSmallEtaleToZariski` is a right adjoint on packaged small commutative
sites. -/
instance (priority := high)
    commSmallEtaleToZariski_sheafPushforwardContinuous_site_isRightAdjoint
    (S : Scheme.{u}) :
    ((commSmallEtaleToZariski S).base.sheafPushforwardContinuous CommRingCat.{u + 1}
      (smallCommRingedSite .zariski S).siteTopology
      (smallCommRingedSite .etale S).siteTopology).IsRightAdjoint := sorry

/-- Module pushforward along `commSmallEtaleToZariski` has a left adjoint. -/
instance (priority := high) commSmallEtaleToZariski_modulePushforward_isRightAdjoint
    (S : Scheme.{u}) :
    ((commSmallEtaleToZariski S).modulePushforward.{u + 1}).IsRightAdjoint := sorry

/-- The commutative presentation of ε is flat, so its module pullback is exact. -/
instance commSmallEtaleToZariski_isFlat (S : Scheme.{u}) :
    RingedSite.Hom.IsFlat.{u + 1} (commSmallEtaleToZariski S) := sorry

/-- The structure-sheaf component of the commutative small-Zariski ringed morphism. -/
noncomputable def zariskiCommStructureSheafMap (f : X ⟶ Y) :
    StandardSmall.commStructureSheaf .zariski Y ⟶
      ((smallZariskiPullback f).sheafPushforwardContinuous CommRingCat.{u + 1}
        (StandardTopology.Small.topology .zariski Y)
        (StandardTopology.Small.topology .zariski X)).obj
        (StandardSmall.commStructureSheaf .zariski X) where
  hom :=
    { app := fun U ↦
        (CommRingCat.universeLift.{u, u + 1}).map
          (Scheme.Γ.map (pullback.fst U.unop.hom f).op)
      naturality := sorry }

/-- At a small Zariski object of `Y`, `zariskiCommStructureSheafMap f` is the
universe lift of global sections of the fibre-product projection. -/
theorem zariskiCommStructureSheafMap_app (f : X ⟶ Y) (U) :
    (zariskiCommStructureSheafMap f).hom.app U =
      (CommRingCat.universeLift.{u, u + 1}).map
        (Scheme.Γ.map (pullback.fst U.unop.hom f).op) := sorry

/-- A scheme morphism induces a morphism of small Zariski ringed sites in the
commutative-ring presentation. -/
noncomputable def zariskiCommRingedHom (f : X ⟶ Y) :
    RingedSite.Hom
      (smallCommRingedSite .zariski X) (smallCommRingedSite .zariski Y) where
  base := smallZariskiPullback f
  isMorphismOfSites := zariskiCommRingedHom_base_isMorphismOfSites f
  structureSheafMap :=
    (sheafCompose (smallCommRingedSite .zariski Y).siteTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (zariskiCommStructureSheafMap f)

/-- The base of `zariskiCommRingedHom f` is small Zariski base change along `f`. -/
theorem zariskiCommRingedHom_base (f : X ⟶ Y) :
    (zariskiCommRingedHom f).base = smallZariskiPullback f := sorry

/-- Continuous pushforward of commutative-ring sheaves along
`zariskiCommRingedHom f` is a right adjoint on unfolded small standard
topologies. -/
instance (priority := high) zariskiCommRingedHom_sheafPushforwardContinuous_isRightAdjoint
    (f : X ⟶ Y) :
    ((zariskiCommRingedHom f).base.sheafPushforwardContinuous CommRingCat.{u + 1}
      (StandardTopology.Small.topology .zariski Y)
      (StandardTopology.Small.topology .zariski X)).IsRightAdjoint := sorry

/-- Continuous pushforward of commutative-ring sheaves along
`zariskiCommRingedHom f` is a right adjoint on packaged small commutative
Zariski sites. -/
instance (priority := high)
    zariskiCommRingedHom_sheafPushforwardContinuous_site_isRightAdjoint
    (f : X ⟶ Y) :
    ((zariskiCommRingedHom f).base.sheafPushforwardContinuous CommRingCat.{u + 1}
      (smallCommRingedSite .zariski Y).siteTopology
      (smallCommRingedSite .zariski X).siteTopology).IsRightAdjoint := sorry

/-- Module pushforward along `zariskiCommRingedHom f` has a left adjoint. -/
instance (priority := high) zariskiCommRingedHom_modulePushforward_isRightAdjoint
    (f : X ⟶ Y) :
    ((zariskiCommRingedHom f).modulePushforward.{u + 1}).IsRightAdjoint := sorry

end AlgebraicGeometry.Scheme.SiteRestriction
