module

public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.Algebra.Category.CommRingCat.Colimits
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.PullbackMixedUniverse
public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback

/-! # Commutative structure sheaves and inverse images on small scheme sites -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule
open AlgebraicGeometry.Scheme.SiteRestriction

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.SiteRestriction

variable {X Y : Scheme.{u}}

/-- The structure-sheaf component of the commutative small Zariski-to-étale
restriction. -/
noncomputable def commSmallEtaleToZariskiStructureSheafMap (S : Scheme.{u}) :
    StandardSmall.commStructureSheaf .zariski S ⟶
      ((smallZariskiToSmallEtale S).sheafPushforwardContinuous CommRingCat.{u + 1}
        S.smallZariskiTopology
        S.smallEtaleTopology).obj
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
          (𝟙 ((Scheme.smallZariskiToScheme S).obj U.unop)).op) := rfl

/-- The commutative-ring restriction morphism between
lifted small ringed sites `(X_étale, 𝒪_étale) ⟶ (X_Zar, 𝒪_X)`. -/
noncomputable def commSmallEtaleToZariski (S : Scheme.{u}) :
    RingedSite.Hom
      (smallCommRingedSite .etale S) (smallCommRingedSite .zariski S) where
  base := smallZariskiToSmallEtale S
  isMorphismOfSites := smallZariskiToSmallEtale_isMorphismOfSites S
  structureSheafMap :=
    (sheafCompose (smallCommRingedSite .zariski S).siteTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (commSmallEtaleToZariskiStructureSheafMap S)

/-- The base of `commSmallEtaleToZariski` is the inclusion of open immersions among
étale morphisms. -/
theorem commSmallEtaleToZariski_base (S : Scheme.{u}) :
    (commSmallEtaleToZariski S).base = smallZariskiToSmallEtale S := rfl

/-- Continuous pushforward of commutative-ring sheaves along
`commSmallEtaleToZariski` is a right adjoint on unfolded small standard
topologies. -/
@[instance high]
theorem commSmallEtaleToZariski_sheafPushforwardContinuous_isRightAdjoint
    (S : Scheme.{u}) :
    ((smallZariskiToSmallEtale S).sheafPushforwardContinuous CommRingCat.{u + 1}
      S.smallZariskiTopology
      S.smallEtaleTopology).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallZariskiToSmallEtale S) CommRingCat.{u + 1}
    S.smallZariskiTopology S.smallEtaleTopology).isRightAdjoint

/-- Module pushforward along `commSmallEtaleToZariski` has a left adjoint. -/
@[instance high]
theorem commSmallEtaleToZariski_modulePushforward_isRightAdjoint
    (S : Scheme.{u}) :
    (SheafOfModules.pushforward.{u + 1, u, u, u + 1, u + 1, u + 1}
      (F := smallZariskiToSmallEtale S)
      (J := S.smallZariskiTopology) (K := S.smallEtaleTopology)
      (S := Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (J := S.smallZariskiTopology)
        (StandardSmall.commStructureSheaf .zariski S))
      (R := Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (J := S.smallEtaleTopology)
        (StandardSmall.commStructureSheaf .etale S))
      ⟨Functor.whiskerRight (commSmallEtaleToZariskiStructureSheafMap S).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩).IsRightAdjoint :=
  (@SheafOfModules.PullbackConstruction.adjunction.{u + 1, u, u, u + 1, u + 1, u + 1}
    _ _ _ _ S.smallZariskiTopology S.smallEtaleTopology
    (smallZariskiToSmallEtale S)
    (Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (J := S.smallZariskiTopology)
      (StandardSmall.commStructureSheaf .zariski S))
    (Sheaf.ringSheafOfComm.{u + 1, u + 1, u} (J := S.smallEtaleTopology)
      (StandardSmall.commStructureSheaf .etale S))
    (smallZariskiToSmallEtale_isContinuous S)
    ⟨Functor.whiskerRight (commSmallEtaleToZariskiStructureSheafMap S).hom
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    (PresheafOfModules.MixedUniversePullback.isRightAdjoint.{u + 1, u}
      (F := smallZariskiToSmallEtale S)
      (R := (Sheaf.ringSheafOfComm.{u + 1, u + 1, u}
        (J := S.smallEtaleTopology) (StandardSmall.commStructureSheaf .etale S)).obj)
      (S := (Sheaf.ringSheafOfComm.{u + 1, u + 1, u}
        (J := S.smallZariskiTopology) (StandardSmall.commStructureSheaf .zariski S)).obj)
      (Functor.whiskerRight (commSmallEtaleToZariskiStructureSheafMap S).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})))
    (StandardTopology.Small.instCommHasWeakSheafify .etale S)
    (StandardTopology.Small.instCommWEqualsLocallyBijective .etale S)).isRightAdjoint

/-- The structure-sheaf component of the commutative small-Zariski ringed morphism. -/
noncomputable def zariskiCommStructureSheafMap (f : X ⟶ Y) :
    StandardSmall.commStructureSheaf .zariski Y ⟶
      ((smallZariskiPullback f).sheafPushforwardContinuous CommRingCat.{u + 1}
        Y.smallZariskiTopology
        X.smallZariskiTopology).obj
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
        (Scheme.Γ.map (pullback.fst U.unop.hom f).op) := rfl

/-- A scheme morphism induces a morphism of small Zariski ringed sites in the
commutative-ring presentation. -/
noncomputable def zariskiCommRingedHom (f : X ⟶ Y) :
    RingedSite.Hom
      (smallCommRingedSite .zariski X) (smallCommRingedSite .zariski Y) where
  base := smallZariskiPullback f
  isMorphismOfSites := Scheme.smallZariskiPullback_isMorphismOfSites f
  structureSheafMap :=
    (sheafCompose (smallCommRingedSite .zariski Y).siteTopology
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (zariskiCommStructureSheafMap f)

/-- The base of `zariskiCommRingedHom f` is small Zariski base change along `f`. -/
theorem zariskiCommRingedHom_base (f : X ⟶ Y) :
    (zariskiCommRingedHom f).base = smallZariskiPullback f := rfl

/-- Continuous pushforward of commutative-ring sheaves along
`zariskiCommRingedHom f` is a right adjoint on unfolded small standard
topologies. -/
@[instance high]
theorem zariskiCommRingedHom_sheafPushforwardContinuous_isRightAdjoint
    (f : X ⟶ Y) :
    ((smallZariskiPullback f).sheafPushforwardContinuous CommRingCat.{u + 1}
      Y.smallZariskiTopology
      X.smallZariskiTopology).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallZariskiPullback f) CommRingCat.{u + 1}
    Y.smallZariskiTopology X.smallZariskiTopology).isRightAdjoint

/-- Continuous pushforward of commutative-ring sheaves along small étale base change
admits an inverse-image left adjoint. -/
@[instance]
theorem smallEtalePullback_sheafPushforwardContinuous_isRightAdjoint (f : X ⟶ Y) :
    ((smallEtalePullback f).sheafPushforwardContinuous CommRingCat.{u + 1}
      Y.smallEtaleTopology
      X.smallEtaleTopology).IsRightAdjoint :=
  (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtalePullback f) CommRingCat.{u + 1}
    Y.smallEtaleTopology
    X.smallEtaleTopology).isRightAdjoint

end AlgebraicGeometry.Scheme.SiteRestriction
