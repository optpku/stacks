module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.RingedSite.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback
public import stacks_project.Chap66.Definition_66_29_1_QCoh
public import stacks_project.Chap84.Lemma_84_7_1_Carrier
public import stacks_project.Chap84.Lemma_84_7_1_Ringed
public import stacks_project.Chap84.Lemma_84_7_1_Sections

/-!
# Quasi-coherent comparison along `π_X` and `a_X`

The associated-module rule `F^a` is identified with `π_X^* F` on the big
étale ringed site and with `a_X^* F` on the big fppf ringed site. The
resulting functors on `QCoh` are equivalences, `ε_{X,*} a_X^* F = π_X^* F`
and `a_{X,*} a_X^* F = F`, and positive higher direct images vanish after
the carrier-universe lift.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.AssociatedModule
open AlgebraicGeometry.AlgebraicSpace.Etale
open AlgebraicGeometry.AlgebraicSpace.Fppf
open RingedSite.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AssociatedModule

variable {S : Scheme.{u}}

/-- The underlying abelian-group presheaf of `π_X^* F`, after the carrier
universe lift to `AddCommGrpCat.{u + 1}`. -/
def piPullbackAb {X : AlgebraicSpace S} (F : X.Modules)
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  underlyingAbPresheaf (overEtaleRingedSite X)
    (moduleCarrierLift (overEtaleRingedSite X)
      ((etalePiRingedHom X).modulePullback.{u}.obj F))

/-- Evaluating `piPullbackAb F` recovers the carrier-lifted underlying abelian
group of `π_X^* F`. -/
theorem piPullbackAb_obj {X : AlgebraicSpace S} (F : X.Modules)
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] (U : Over X) :
    (piPullbackAb F).obj (op U) =
      (underlyingAbPresheaf (overEtaleRingedSite X)
        (moduleCarrierLift (overEtaleRingedSite X)
          ((etalePiRingedHom X).modulePullback.{u}.obj F))).obj (op U) :=
  rfl

/-- The associated abelian-group rule is isomorphic to `π_X^* F` on
`(Spaces/X)_étale`, after the carrier-universe lift. -/
theorem piPullbackIso {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    IsIsomorphic (piPullbackAb F) (associatedPresheaf F) :=
  sorry

/-- The underlying abelian-group presheaf of `a_X^* F`, after the carrier
universe lift to `AddCommGrpCat.{u + 1}`. -/
def aPullbackAb {X : AlgebraicSpace S} (F : X.Modules)
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (Over X)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} :=
  underlyingAbPresheaf (overFppfRingedSite X)
    (moduleCarrierLift (overFppfRingedSite X)
      ((aRingedHom X).modulePullback.{u}.obj F))

/-- Evaluating `aPullbackAb F` recovers the carrier-lifted underlying abelian
group of `a_X^* F`. -/
theorem aPullbackAb_obj {X : AlgebraicSpace S} (F : X.Modules)
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] (U : Over X) :
    (aPullbackAb F).obj (op U) =
      (underlyingAbPresheaf (overFppfRingedSite X)
        (moduleCarrierLift (overFppfRingedSite X)
          ((aRingedHom X).modulePullback.{u}.obj F))).obj (op U) :=
  rfl

/-- The associated abelian-group rule is isomorphic to `a_X^* F` on
`(Spaces/X)_fppf`, after the carrier-universe lift. -/
theorem aPullbackIso {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    IsIsomorphic (aPullbackAb F) (associatedPresheaf F) :=
  sorry

/-- Quasi-coherence of `π_X^* F` on the big étale ringed site. -/
instance piPullback_isQuasicoherent {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    ((etalePiRingedHom X).modulePullback.{u}.obj F).IsQuasicoherent :=
  sorry

/-- Quasi-coherence of `a_X^* F` on the big fppf ringed site. -/
instance aPullback_isQuasicoherent {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    ((aRingedHom X).modulePullback.{u}.obj F).IsQuasicoherent :=
  sorry

/-- The functor sending a quasi-coherent `𝒪_X`-module to its associated
quasi-coherent module `π_X^* F` on `((Spaces/X)_étale, 𝒪)`. -/
def associatedFunctor_etale (X : AlgebraicSpace S)
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    QCoh X ⥤
      (SheafOfModules.isQuasicoherent (overEtaleStructureSheaf X)).FullSubcategory where
  obj F :=
    ⟨(etalePiRingedHom X).modulePullback.{u}.obj F.obj, inferInstance⟩
  map {F G} φ :=
    ⟨(etalePiRingedHom X).modulePullback.{u}.map φ.hom⟩
  map_id := sorry
  map_comp := sorry

/-- The underlying module sheaf of `associatedFunctor_etale X` at `F` is
`π_X^* F.obj`. -/
theorem associatedFunctor_etale_obj (X : AlgebraicSpace S)
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] (F : QCoh X) :
    ((associatedFunctor_etale X).obj F).obj =
      (etalePiRingedHom X).modulePullback.{u}.obj F.obj :=
  rfl

/-- The functor `F ↦ π_X^* F` is an equivalence between quasi-coherent
`𝒪_X`-modules and quasi-coherent modules on `((Spaces/X)_étale, 𝒪)`. -/
instance associatedFunctor_etale_isEquivalence (X : AlgebraicSpace S)
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (associatedFunctor_etale X).IsEquivalence :=
  sorry

/-- The functor sending a quasi-coherent `𝒪_X`-module to its associated
quasi-coherent module `a_X^* F` on `((Spaces/X)_fppf, 𝒪)`. -/
def associatedFunctor_fppf (X : AlgebraicSpace S)
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    QCoh X ⥤
      (SheafOfModules.isQuasicoherent (overFppfStructureSheaf X)).FullSubcategory where
  obj F :=
    ⟨(aRingedHom X).modulePullback.{u}.obj F.obj, inferInstance⟩
  map {F G} φ :=
    ⟨(aRingedHom X).modulePullback.{u}.map φ.hom⟩
  map_id := sorry
  map_comp := sorry

/-- The underlying module sheaf of `associatedFunctor_fppf X` at `F` is
`a_X^* F.obj`. -/
theorem associatedFunctor_fppf_obj (X : AlgebraicSpace S)
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] (F : QCoh X) :
    ((associatedFunctor_fppf X).obj F).obj =
      (aRingedHom X).modulePullback.{u}.obj F.obj :=
  rfl

/-- The functor `F ↦ a_X^* F` is an equivalence between quasi-coherent
`𝒪_X`-modules and quasi-coherent modules on `((Spaces/X)_fppf, 𝒪)`. -/
instance associatedFunctor_fppf_isEquivalence (X : AlgebraicSpace S)
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    (associatedFunctor_fppf X).IsEquivalence :=
  sorry

/-- Pushing `a_X^* F` forward along `ε_X` recovers `π_X^* F`. -/
theorem epsilon_pushforward_aPullbackIso {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(etalePiRingedHom X).modulePushforward.{u}.IsRightAdjoint]
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    IsIsomorphic
      ((epsilonRingedHom X).modulePushforward.{u}.obj
        ((aRingedHom X).modulePullback.{u}.obj F))
      ((etalePiRingedHom X).modulePullback.{u}.obj F) :=
  sorry

/-- Pushing `a_X^* F` forward along `a_X` recovers `F`. -/
theorem a_pushforward_aPullbackIso {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(aRingedHom X).modulePushforward.{u}.IsRightAdjoint] :
    IsIsomorphic
      ((aRingedHom X).modulePushforward.{u}.obj
        ((aRingedHom X).modulePullback.{u}.obj F))
      F :=
  sorry

/-- Positive higher direct images of `a_X^* F` along `ε_X` vanish, after the
carrier lift required by the size condition. -/
theorem epsilon_higherDirectImage_vanishes {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [HasInjectiveResolutions (RingedSite.ModuleCat.{u + 1} (overFppfRingedSite X))] :
    ∀ i : ℕ, 0 < i →
      IsZero
        (higherDirectImageModule (epsilonRingedHom X)
          ((aRingedHom X).modulePullback.{u + 1}.obj
            (moduleCarrierLift (ringedSite X) F))
          i) :=
  sorry

/-- Positive higher direct images of `a_X^* F` along `a_X` vanish, after the
carrier lift required by the size condition. -/
theorem a_higherDirectImage_vanishes {X : AlgebraicSpace S} (F : X.Modules)
    [F.IsQuasicoherent]
    [(aRingedHom X).modulePushforward.{u + 1}.IsRightAdjoint]
    [HasInjectiveResolutions (RingedSite.ModuleCat.{u + 1} (overFppfRingedSite X))] :
    ∀ i : ℕ, 0 < i →
      IsZero
        (higherDirectImageModule (aRingedHom X)
          ((aRingedHom X).modulePullback.{u + 1}.obj
            (moduleCarrierLift (ringedSite X) F))
          i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.AssociatedModule

end

end
