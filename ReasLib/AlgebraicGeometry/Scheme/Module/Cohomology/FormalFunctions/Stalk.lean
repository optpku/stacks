/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.ExactSquare
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Sites.Cohomology.Map
public import ReasLib.Topology.Sheaf.Pushforward
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Topology.Category.TopCat.OpenNhds
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Exact
public import ReasLib.Topology.Sheaf.HigherDirectImage.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.FiberNeighbourhood

/-!
# Formal functions on stalks

The cohomology of infinitesimal fibre neighbourhoods forms an inverse system of
modules over the completed local ring. The canonical maps from the
higher-direct-image stalk descend through maximal-ideal powers and extend to a
map from its completion to the inverse limit. For a proper morphism to a locally
Noetherian scheme and a coherent sheaf, this map is an isomorphism.

Stage `n` uses the quotient by the `(n + 1)`st power of the maximal ideal;
stage `0` is the scheme-theoretic fibre.
-/

-- Public maps use private coefficient adapters in their implementations.
set_option backward.privateInPublic true

@[expose] public section

open CategoryTheory CategoryTheory.ConcreteCategory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open IsLocalRing
open TopologicalSpace TopologicalSpace.OpenNhds

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace FiberNeighbourhood

section

variable {X Y : Scheme.{u}}

/-- The completed local ring `𝒪_{Y,y}^∧`. -/
abbrev completedRing (y : Y) : Type u :=
  AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)

/-- Pullback along a neighbourhood transition recovers the thinner neighbourhood sheaf. -/
def sheafPullbackIso (f : X ⟶ Y) (F : X.Modules) (y : Y) (n : ℕ) :
    (Scheme.Modules.pullback (schemeTransition f y n)).obj (sheaf f F y (n + 1)) ≅
      sheaf f F y n :=
  (Scheme.Modules.pullbackComp (schemeTransition f y n) (ι f y (n + 1))).app F ≪≫
    (Scheme.Modules.pullbackCongr (schemeTransition_ι f y n)).app F

/-- The adjunction unit followed by `sheafPullbackIso`, as a map of sheaves on the thicker
neighbourhood. -/
def sheafTransitionUnit (f : X ⟶ Y) (F : X.Modules) (y : Y) (n : ℕ) :
    sheaf f F y (n + 1) ⟶
      (Scheme.Modules.pushforward (schemeTransition f y n)).obj (sheaf f F y n) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (schemeTransition f y n)).unit.app
      (sheaf f F y (n + 1)) ≫
    (Scheme.Modules.pushforward (schemeTransition f y n)).map (sheafPullbackIso f F y n).hom

/-- Degree-`p` additive cohomology of the infinitesimal neighbourhood, with scalars
restricted along its quotient-spectrum structure morphism. -/
abbrev homCohomology (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    ModuleCat (quotientRing y n) :=
  (ModuleCat.restrictScalars (globalSectionsMap (toSpec f y n))).obj
    (RingedSpace.moduleCohomologyWithScalars (sheaf f F y n) p)

/-- Evaluation at exponent `n+1` factors as evaluation at `n+2` followed by `quotientStep`. -/
theorem evalₐ_comp_quotientStep (y : Y) (n : ℕ) :
    (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)).toRingHom =
      (quotientStep y n).comp
        (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 2)).toRingHom :=
  sorry

/-- Degree-`p` cohomology of an infinitesimal neighbourhood, as an `𝒪_{Y,y}^∧`-module. -/
abbrev cohomology (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    ModuleCat (completedRing y) :=
  (ModuleCat.restrictScalars
      (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)).toRingHom).obj
    (homCohomology f F y p n)

/-- Neighbourhood cohomology is restriction of scalars of affine-base cohomology along
`evalₐ m_y^{n+1}`. -/
theorem cohomology_eq (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    cohomology f F y p n =
      (ModuleCat.restrictScalars
          (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)).toRingHom).obj
        (homCohomology f F y p n) :=
  sorry

/-- Global-sections maps of successive structure morphisms commute with `quotientStep`. -/
theorem globalSectionsMap_comp_quotientStep (f : X ⟶ Y) (y : Y) (n : ℕ) :
    (globalSectionsMap (toSpec f y n)).comp (quotientStep y n) =
      (sectionsMapAlong (schemeTransition f y n) ⊤ ⊤ le_top).comp
        (globalSectionsMap (toSpec f y (n + 1))) :=
  sorry

/-- The underlying additive sheaf of a module pushforward is the topological
pushforward of the underlying additive sheaf. -/
private def modulePushforwardToSheafIso {X Y : Scheme.{u}} (g : X ⟶ Y) (F : X.Modules) :
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj
        ((Scheme.Modules.pushforward g).obj F) ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) where
  hom :=
    InducedCategory.homMk
      { app := fun U ↦ 𝟙 _
        naturality := fun _ _ _ ↦ sorry }
  inv :=
    InducedCategory.homMk
      { app := fun U ↦ 𝟙 _
        naturality := fun _ _ _ ↦ sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Forgetting module pushforward to additive sheaves commutes naturally with pushforward. -/
private def modulePushforwardToSheafNatIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Scheme.Modules.pushforward g ⋙ SheafOfModules.toSheaf Y.ringCatSheaf ≅
      SheafOfModules.toSheaf X.ringCatSheaf ⋙
        TopCat.Sheaf.pushforward AddCommGrpCat.{u} g.base :=
  NatIso.ofComponents (fun F ↦ modulePushforwardToSheafIso g F) fun _ ↦ sorry

/-- Direct-image cohomology over `⊤` recovers neighbourhood cohomology after
`Opens.map_top`. -/
theorem pushforwardCohomologyMap_top_eq (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj (sheaf f F y n)).H' p
        ((Opens.map (schemeTransition f y n).base).obj ⊤) =
      RingedSpace.moduleCohomology (sheaf f F y n) p :=
  sorry

/-- Additive successor restriction `H^p(X_{n+2}, ℱ_{n+2}) ⟶ H^p(X_{n+1}, ℱ_{n+1})`. -/
def sheafCohomologyStep (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    RingedSpace.moduleCohomology (sheaf f F y (n + 1)) p ⟶
      RingedSpace.moduleCohomology (sheaf f F y n) p := by
  exact
    RingedSpace.moduleCohomologyMap (sheafTransitionUnit f F y n) p ≫
      CategoryTheory.Sheaf.cohomologyMap
        (modulePushforwardToSheafIso (schemeTransition f y n) (sheaf f F y n)).hom p ⊤ ≫
      CategoryTheory.Sheaf.pushforwardCohomologyMap
        (schemeTransition f y n).base
        ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj (sheaf f F y n))
        p ⊤ ≫
      eqToHom (pushforwardCohomologyMap_top_eq f F y p n)

/-- Underlying function of successor restriction of neighbourhood cohomology. -/
def homCohomologyStepFun (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    homCohomology f F y p (n + 1) → homCohomology f F y p n :=
  (sheafCohomologyStep f F y p n).hom

/-- Successor restriction of neighbourhood cohomology is semilinear along `quotientStep`. -/
def homCohomologyStepSemilinear (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    homCohomology f F y p (n + 1) →ₛₗ[quotientStep y n]
      (homCohomology f F y p n) where
  toFun := homCohomologyStepFun f F y p n
  map_add' := sorry
  map_smul' := sorry

/-- Successor restriction of neighbourhood cohomology as modules over
`𝒪_{Y,y} ⧸ m_y^{n+2}`. -/
def homCohomologyStep (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    homCohomology f F y p (n + 1) ⟶
      (ModuleCat.restrictScalars (quotientStep y n)).obj (homCohomology f F y p n) :=
  ModuleCat.semilinearMapAddEquiv (quotientStep y n)
      (homCohomology f F y p (n + 1)) (homCohomology f F y p n)
    (homCohomologyStepSemilinear f F y p n)

/-- Successor restriction of neighbourhood cohomology as `𝒪_{Y,y}^∧`-modules. -/
def cohomologyStep (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    cohomology f F y p (n + 1) ⟶ cohomology f F y p n :=
  (ModuleCat.restrictScalars
      (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 2)).toRingHom).map
    (homCohomologyStep f F y p n) ≫
    (ModuleCat.restrictScalarsComp'App
        (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 2)).toRingHom
        (quotientStep y n)
        (AdicCompletion.evalₐ (maximalIdeal (Y.presheaf.stalk y)) (n + 1)).toRingHom
        (evalₐ_comp_quotientStep y n) (homCohomology f F y p n)).inv

/-- The inverse system `n ↦ H^p(X_{n+1}, ℱ_{n+1})` in `𝒪_{Y,y}^∧`-modules. -/
def tower (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) :
    SequentialInverseSystem (ModuleCat (completedRing y)) :=
  Functor.ofOpSequence (cohomologyStep f F y p)

/-- The cohomology tower evaluates to the named neighbourhood cohomology stage. -/
theorem tower_obj (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (tower f F y p).obj (op n) = cohomology f F y p n :=
  sorry

/-- Successor transitions of the cohomology tower are `cohomologyStep`. -/
theorem tower_stepMap (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (tower f F y p).stepMap n = cohomologyStep f F y p n :=
  sorry

end

section

section ComparisonData

variable {X Y : Scheme.{u}}

/-- The `m_y`-adic completion of the stalk `(R^p f_* ℱ)_y`. -/
abbrev completedStalk (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) : Type u :=
  AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
    (RingedSpace.stalkModuleCat
      (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y)

/-- The completed stalk is the adic completion of the higher-direct-image stalk. -/
theorem completedStalk_eq (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) :
    completedStalk f F y p =
      AdicCompletion (maximalIdeal (Y.presheaf.stalk y))
        (RingedSpace.stalkModuleCat
          (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y) :=
  sorry

/-- The adjunction unit `ℱ ⟶ i_{n+1,*} i_{n+1}^* ℱ`. -/
private def unitToPushed (f : X ⟶ Y) (F : X.Modules) (y : Y) (n : ℕ) :
    F ⟶ (Scheme.Modules.pushforward (ι f y n)).obj (sheaf f F y n) :=
  (Scheme.Modules.pullbackPushforwardAdjunction (ι f y n)).unit.app F

/-- The stalk `𝒪_{Y,y}` acts on neighbourhood cohomology through the quotient map. -/
instance instModuleStalkHomCohomology
    (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    Module (Y.presheaf.stalk y) (homCohomology f F y p n) :=
  Module.compHom _ (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))

/-- Additive identification of the bundled higher-direct-image stalk with the
presheaf stalk. -/
private theorem higherDirectImageStalk_eq (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) :
    (forget₂ (ModuleCat (Y.presheaf.stalk y)) AddCommGrpCat.{u}).obj
        (RingedSpace.stalkModuleCat
          (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y) =
      TopCat.Presheaf.stalk
        (RingedSpace.Hom.higherDirectImageModule f.toShHom F p).val.presheaf y :=
  sorry

-- Unfold the scheme module-category aliases to reuse the canonical sheaf-functor instances.
set_option backward.isDefEq.respectTransparency false in
/-- The exact additive square compares module-valued higher direct images with
higher direct images of the underlying additive sheaf. -/
private def higherDirectImageUnderlyingMap (f : X ⟶ Y) (F : X.Modules) (p : ℕ) :
    (SheafOfModules.toSheaf Y.ringCatSheaf).obj
        (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) ⟶
      TopCat.Sheaf.higherDirectImage f.base
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) p :=
  @Functor.RightDerived.exactSquareApp
    X.Modules inferInstance inferInstance inferInstance
    Y.Modules inferInstance inferInstance
    (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})
      inferInstance inferInstance inferInstance
    (Sheaf (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u})
      inferInstance inferInstance
    (Scheme.Modules.pushforward f)
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f.base) inferInstance
    (by apply TopCat.Sheaf.pushforward_additive_of_abelian)
    (SheafOfModules.toSheaf X.ringCatSheaf)
    (SheafOfModules.toSheaf Y.ringCatSheaf)
    (inferInstanceAs (SheafOfModules.toSheaf.{u} X.ringCatSheaf).Additive)
    (inferInstanceAs (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).Additive)
    (inferInstanceAs (PreservesFiniteLimits (SheafOfModules.toSheaf.{u} X.ringCatSheaf)))
    (SheafOfModules.toSheaf_preservesFiniteColimits X.ringCatSheaf)
    (SheafOfModules.toSheaf_preservesFiniteColimits Y.ringCatSheaf)
    (modulePushforwardToSheafNatIso f).hom p F

/-- The coefficient map from the additive inverse image to the underlying sheaf of the
module pullback is adjoint to the module pullback unit. -/
private def neighbourhoodCoefficientMap (f : X ⟶ Y) (F : X.Modules) (y : Y) (n : ℕ) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} (ι f y n).base).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ⟶
      (SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj (sheaf f F y n) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (ι f y n).base).homEquiv _ _).symm
    ((SheafOfModules.toSheaf X.ringCatSheaf).map (unitToPushed f F y n) ≫
      (modulePushforwardToSheafIso (ι f y n) (sheaf f F y n)).hom)

/-- Pullback of cohomology from open neighbourhoods of the base point forms a cocone
with vertex the additive cohomology of an infinitesimal fibre neighbourhood. -/
private def neighbourhoodCohomologyCocone
    (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    Cocone (TopCat.Sheaf.Cohomology.SpecializingPreimage.diagram f.base y
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) p) where
  pt := RingedSpace.moduleCohomology (sheaf f F y n) p
  ι :=
    { app := fun U ↦
        CategoryTheory.Sheaf.pullbackCohomologyMap (ι f y n).base
            ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) p
            ((Opens.map f.base).obj U.unop.1) ≫
          CategoryTheory.Sheaf.cohomologyMap (neighbourhoodCoefficientMap f F y n) p
            ((Opens.map (ι f y n).base).obj ((Opens.map f.base).obj U.unop.1)) ≫
          eqToHom (congrArg
            (fun V ↦ ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
              (sheaf f F y n)).H' p V)
            (preimage_neighbourhood_eq_top f y n U.unop))
      naturality := fun _ _ _ ↦ sorry }

/-- The stalk comparison obtained from the additive higher-direct-image comparison
and pullback from each open neighbourhood to the infinitesimal fibre neighbourhood. -/
def toHomCohomologyFun (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    RingedSpace.stalkModuleCat
      (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y →
      homCohomology f F y p n := by
  exact fun m ↦
    (eqToHom (higherDirectImageStalk_eq f F y p) ≫
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).map
        ((TopCat.Sheaf.forget AddCommGrpCat.{u} Y.carrier).map
          (higherDirectImageUnderlyingMap f F p)) ≫
      (TopCat.Sheaf.HigherDirectImage.Stalk.cohomologyIso f.base y
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) p).inv ≫
      colimit.desc _ (neighbourhoodCohomologyCocone f F y p n)).hom m

/-- The comparison from the higher-direct-image stalk to neighbourhood cohomology is
semilinear along the quotient map `𝒪_{Y,y} ⟶ 𝒪_{Y,y} ⧸ m_y^{n+1}`. -/
def toHomCohomologySemilinear (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    RingedSpace.stalkModuleCat
        (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y →ₛₗ[
          Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1))]
      (homCohomology f F y p n) where
  toFun := toHomCohomologyFun f F y p n
  map_add' := sorry
  map_smul' := sorry

/-- The canonical map from the higher-direct-image stalk to neighbourhood cohomology as an
`𝒪_{Y,y}`-module. -/
def toHomCohomology (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    RingedSpace.stalkModuleCat
      (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y ⟶
      (ModuleCat.restrictScalars
        (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))).obj
        (homCohomology f F y p n) :=
  ModuleCat.semilinearMapAddEquiv
      (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))
      (RingedSpace.stalkModuleCat
        (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y)
      (homCohomology f F y p n)
    (toHomCohomologySemilinear f F y p n)

/-- `m_y^{n+1}` annihilates the image of `toHomCohomology`. -/
theorem pow_smul_le_ker_toHomCohomology (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    maximalIdeal (Y.presheaf.stalk y) ^ (n + 1) •
        (⊤ : Submodule (Y.presheaf.stalk y)
          (RingedSpace.stalkModuleCat
            (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y)) ≤
      LinearMap.ker (toHomCohomology f F y p n).hom :=
  sorry

/-- The descended comparison
`(R^p f_* ℱ)_y ⧸ m_y^{n+1} • ⊤ ⟶ H^p(X_{n+1}, ℱ_{n+1})`. -/
def toHomCohomologyModPow (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    ModuleCat.of (Y.presheaf.stalk y)
      (RingedSpace.stalkModuleCat
          (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y ⧸
        maximalIdeal (Y.presheaf.stalk y) ^ (n + 1) •
          (⊤ : Submodule (Y.presheaf.stalk y)
            (RingedSpace.stalkModuleCat
              (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y))) ⟶
      (ModuleCat.restrictScalars
        (Ideal.Quotient.mk (maximalIdeal (Y.presheaf.stalk y) ^ (n + 1)))).obj
        (homCohomology f F y p n) :=
  ConcreteCategory.ofHom
    ((maximalIdeal (Y.presheaf.stalk y) ^ (n + 1) •
        (⊤ : Submodule (Y.presheaf.stalk y)
          (RingedSpace.stalkModuleCat
            (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y))).liftQ
      (toHomCohomology f F y p n).hom (pow_smul_le_ker_toHomCohomology f F y p n))

/-- The underlying function of the completed-stalk comparison at stage `n`. -/
def toStageFun (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    completedStalk f F y p → cohomology f F y p n :=
  fun x ↦
    (toHomCohomologyModPow f F y p n).hom
      (AdicCompletion.eval (maximalIdeal (Y.presheaf.stalk y))
        (RingedSpace.stalkModuleCat
          (RingedSpace.Hom.higherDirectImageModule f.toShHom F p) y)
        (n + 1) x)

/-- The underlying function of `toStage` is linear over `𝒪_{Y,y}^∧`. -/
theorem isLinearMap_toStageFun (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    IsLinearMap (completedRing y) (toStageFun f F y p n) :=
  sorry

/-- The stage map from the completed stalk to neighbourhood cohomology, as
`𝒪_{Y,y}^∧`-modules. -/
def toStage (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    ModuleCat.of (completedRing y) (completedStalk f F y p) ⟶ cohomology f F y p n :=
  ConcreteCategory.ofHom
    (IsLinearMap.mk' (toStageFun f F y p n) (isLinearMap_toStageFun f F y p n))

/-- Stage maps from the completed stalk are natural with respect to the cohomology tower. -/
theorem toStage_natural (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) (n : ℕ) :
    toStage f F y p (n + 1) ≫ cohomologyStep f F y p n = toStage f F y p n :=
  sorry

/-- The induced map from the completed higher-direct-image stalk to the inverse
limit of neighbourhood cohomology. -/
def limitComparison (f : X ⟶ Y) (F : X.Modules) (y : Y) (p : ℕ) :
    ModuleCat.of (completedRing y) (completedStalk f F y p) ⟶ limit (tower f F y p) :=
  limit.lift (tower f F y p)
    { pt := ModuleCat.of (completedRing y) (completedStalk f F y p)
      π :=
        { app := fun n ↦ toStage f F y p n.unop
          naturality := fun _ _ _ ↦ sorry } }

/-- Projecting `limitComparison` to stage `n` recovers `toStage`. -/
theorem limitComparison_comp_π (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    limitComparison f F y p ≫ limit.π (tower f F y p) (op n) = toStage f F y p n :=
  sorry

end ComparisonData

end

variable {X Y : Scheme.{u}}
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- For a proper morphism to a locally Noetherian scheme and a coherent sheaf,
the canonical map from the completed higher-direct-image stalk to the inverse
limit of infinitesimal-neighbourhood cohomology is an isomorphism of modules
over the completed local ring. -/
instance isIso_limitComparison [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsProper f]
    (F : X.Modules) [F.IsCoherent] (y : Y) (p : ℕ) :
    IsIso (limitComparison f F y p) :=
  sorry

end FiberNeighbourhood
end AlgebraicGeometry.Scheme.Hom
