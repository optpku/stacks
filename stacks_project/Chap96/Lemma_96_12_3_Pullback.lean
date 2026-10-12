/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Projection
public import stacks_project.Chap96.Lemma_96_12_4_EtaleModules
public import stacks_project.Chap96.Lemma_96_12_4_LQCoh

/-!
# Étale module inverse image along a 1-morphism of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` induces
`f^* = f⁻¹` on étale modules by `SheafOfModules.pushforward` along the
coefficient map `𝒪_X ⟶ f⁻¹ 𝒪_Y`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Functor FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The projection of a category fibred in groupoids is continuous for the associated
étale topology. -/
instance etaleProjection_isContinuous (X : GroupoidsOver S) :
    X.p.IsContinuous X.etaleTopology (StandardTopology.etale.overTopology S) :=
  Functor.inheritedTopology.isContinuous X.p (StandardTopology.etale.overTopology S)

variable {X Y : GroupoidsOver S}

/-- A 1-morphism of categories fibred in groupoids is continuous for the associated
étale topologies. -/
instance toFunctor_etale_isContinuous (f : X ⟶ Y) :
    (toFunctor f).IsContinuous X.etaleTopology Y.etaleTopology :=
  CartesianBasedFunctor.inheritedTopology.isContinuous (toCartesianBasedFunctor f)
    (StandardTopology.etale.overTopology S)

/-- The identification `f⁻¹ 𝒪_Y ≅ 𝒪_X` of commutative étale structure sheaves. -/
def commEtaleStructureSheafIso (f : X ⟶ Y) :
    ((toFunctor f).sheafPushforwardContinuous CommRingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (commEtaleStructureSheaf Y) ≅
      commEtaleStructureSheaf X :=
  (sheafPushforwardContinuousComp' (eqToIso (comm f)) CommRingCat.{u}
      X.etaleTopology Y.etaleTopology
      (StandardTopology.etale.overTopology S)).app bigEtaleCommStructureSheaf

/-- `commEtaleStructureSheafIso` is the continuous-pushforward comparison along `comm f`. -/
theorem commEtaleStructureSheafIso_eq (f : X ⟶ Y) :
    commEtaleStructureSheafIso f =
      (sheafPushforwardContinuousComp' (eqToIso (comm f)) CommRingCat.{u}
          X.etaleTopology Y.etaleTopology
          (StandardTopology.etale.overTopology S)).app bigEtaleCommStructureSheaf :=
  sorry

/-- Comparison of underlying ring sheaves: `ringSheafOfComm (f⁻¹ 𝒪_Y) ≅ f⁻¹ (ringSheafOfComm 𝒪_Y)`. -/
def inverseImageEtaleStructureSheafIso (f : X ⟶ Y) :
    CategoryTheory.Sheaf.ringSheafOfComm.{u, u + 1, u}
      (((toFunctor f).sheafPushforwardContinuous CommRingCat.{u}
          X.etaleTopology Y.etaleTopology).obj (commEtaleStructureSheaf Y)) ≅
      ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleStructureSheaf Y) :=
  (fullyFaithfulSheafToPresheaf X.etaleTopology RingCat.{u}).preimageIso (Iso.refl _)

/-- `inverseImageEtaleStructureSheafIso` identifies the ring sheaf of the inverse image
with the inverse image of the ring sheaf. -/
theorem inverseImageEtaleStructureSheafIso_eq (f : X ⟶ Y) :
    inverseImageEtaleStructureSheafIso f =
      (fullyFaithfulSheafToPresheaf X.etaleTopology RingCat.{u}).preimageIso (Iso.refl _) :=
  sorry

/-- The coefficient morphism `𝒪_X ⟶ f⁻¹ 𝒪_Y` obtained from `commEtaleStructureSheafIso`. -/
def etaleStructureSheafMap (f : X ⟶ Y) :
    etaleStructureSheaf X ⟶
      ((toFunctor f).sheafPushforwardContinuous RingCat.{u}
        X.etaleTopology Y.etaleTopology).obj (etaleStructureSheaf Y) :=
  CategoryTheory.Sheaf.ringSheafOfCommMap.{u, u + 1, u} (commEtaleStructureSheafIso f).inv ≫
    (inverseImageEtaleStructureSheafIso f).hom

/-- The coefficient morphism `𝒪_X ⟶ f⁻¹ 𝒪_Y` is an isomorphism, so `f^* = f⁻¹`. -/
theorem etaleStructureSheafMap_isIso (f : X ⟶ Y) :
    IsIso (etaleStructureSheafMap f) :=
  sorry

/-- The pullback functor `f^* = f⁻¹ : Mod(Y_étale, 𝒪_Y) ⟶ Mod(X_étale, 𝒪_X)`. -/
def moduleInverseImage (f : X ⟶ Y) :
    etaleModules Y ⥤ etaleModules X :=
  SheafOfModules.pushforward.{u} (etaleStructureSheafMap f)

/-- `moduleInverseImage f` is module inverse image along `etaleStructureSheafMap f`. -/
theorem moduleInverseImage_eq (f : X ⟶ Y) :
    moduleInverseImage f = SheafOfModules.pushforward.{u} (etaleStructureSheafMap f) :=
  sorry

/-- Restriction of `G` at `(toFunctor f).obj x`, transported to the small étale site of `p(x)`
along `toFunctor f ⋙ Y.p = X.p`. -/
def restrictToSmallEtale_toFunctor (f : X ⟶ Y) (x : X.total) (G : etaleModules Y) :
    RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite (X.p.obj x).left) :=
  eqToHom
    (congrArg (fun U : Over S =>
        RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite U.left))
      (congrArg (fun F : X.total ⥤ Over S => F.obj x) (comm f)))
    ((restrictModulesToSmallEtale Y ((toFunctor f).obj x)).obj G)

/-- `restrictToSmallEtale_toFunctor` is transport of the small-étale restriction along `comm f`. -/
theorem restrictToSmallEtale_toFunctor_eq (f : X ⟶ Y) (x : X.total) (G : etaleModules Y) :
    restrictToSmallEtale_toFunctor f x G =
      eqToHom
        (congrArg (fun U : Over S =>
            RingedSite.ModuleCat.{u} (Scheme.Etale.Small.ringedSite U.left))
          (congrArg (fun F : X.total ⥤ Over S => F.obj x) (comm f)))
        ((restrictModulesToSmallEtale Y ((toFunctor f).obj x)).obj G) :=
  sorry

/-- Restriction of `f^* G` at `x` is canonically isomorphic to restriction of `G` at
`(toFunctor f).obj x`, after transport along `comm f`. -/
theorem restrictToSmallEtale_moduleInverseImage (f : X ⟶ Y) (x : X.total)
    (G : etaleModules Y) :
    Nonempty
      ((restrictModulesToSmallEtale X x).obj ((moduleInverseImage f).obj G) ≅
        restrictToSmallEtale_toFunctor f x G) :=
  sorry

end AlgebraicGeometry.GroupoidsOver


