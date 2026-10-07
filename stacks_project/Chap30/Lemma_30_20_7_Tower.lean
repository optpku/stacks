module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Map
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.ExactSquare
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import ReasLib.CategoryTheory.Sites.Cohomology.Map
public import ReasLib.CategoryTheory.Sites.Cohomology.SectionsComparison
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
public import ReasLib.CategoryTheory.Sites.Cohomology.Zero
public import stacks_project.Chap30.Lemma_30_20_7_Neighbourhood

/-!
# Cohomology tower of infinitesimal fibre neighbourhoods

The inverse system `n ↦ H^p(X_{n+1}, ℱ_{n+1})` is affine-base cohomology
`Hom.cohomology (toSpec f y n) (sheaf f F y n) p`, viewed as an
`𝒪_{Y,y} ⧸ m_y^{n+1}`-module and as an `𝒪_{Y,y}^∧`-module along
`AdicCompletion.evalₐ m_y^{n+1}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ConcreteCategory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Hom.FiberNeighbourhood
open IsLocalRing
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace FiberNeighbourhood

/-- The underlying-additive-sheaf functor is additive. -/
instance toSheaf_additive (Z : Scheme.{u}) :
    (SheafOfModules.toSheaf Z.ringCatSheaf).Additive :=
  sorry

/-- The underlying-additive-sheaf functor preserves homology. -/
instance toSheaf_preservesHomology (Z : Scheme.{u}) :
    (SheafOfModules.toSheaf Z.ringCatSheaf).PreservesHomology :=
  sorry

/-- The underlying-additive-sheaf functor preserves finite colimits. -/
instance toSheaf_preservesFiniteColimits (Z : Scheme.{u}) :
    PreservesFiniteColimits (SheafOfModules.toSheaf Z.ringCatSheaf) :=
  sorry

/-- Additive sheaves on a scheme admit injective resolutions. -/
instance hasInjectiveResolutions_sheaf (Z : Scheme.{u}) :
    HasInjectiveResolutions
      (Sheaf (Opens.grothendieckTopology Z.carrier) AddCommGrpCat.{u}) :=
  sorry

/-- Forgotten module-valued sections on an open are sections of the underlying additive sheaf. -/
def moduleSectionsAsAbelianIso (Z : Scheme.{u}) (U : Opens Z) :
    RingedSpace.moduleSectionsAsAbelianFunctor Z.toRingedSpace U ≅
      SheafOfModules.toSheaf Z.ringCatSheaf ⋙
        siteAbelianSectionsFunctor (Opens.grothendieckTopology Z.carrier) U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ sorry

/-- Exactness of `toSheaf` identifies deriving `toSheaf ⋙ Γ(U, -)` with derived sections of
the underlying additive sheaf. -/
theorem toSheafCompSectionsRightDerived_obj_eq (Z : Scheme.{u}) (U : Opens Z) (p : ℕ)
    (G : Z.Modules) :
    ((SheafOfModules.toSheaf Z.ringCatSheaf ⋙
        siteAbelianSectionsFunctor (Opens.grothendieckTopology Z.carrier) U).rightDerived p).obj G =
      ((siteAbelianSectionsFunctor (Opens.grothendieckTopology Z.carrier) U).rightDerived p).obj
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj G) :=
  sorry

/-- Exactness of `toSheaf` compares `(toSheaf ⋙ Γ(U, -)).rightDerived p` with derived
sections of `toSheaf.obj G`. The forward map is the exact-square comparison; the reverse is
the corresponding object identification. -/
def toSheafCompSectionsRightDerivedIso (Z : Scheme.{u}) (U : Opens Z) (p : ℕ)
    (G : Z.Modules) :
    ((SheafOfModules.toSheaf Z.ringCatSheaf ⋙
        siteAbelianSectionsFunctor (Opens.grothendieckTopology Z.carrier) U).rightDerived p).obj G ≅
      ((siteAbelianSectionsFunctor (Opens.grothendieckTopology Z.carrier) U).rightDerived p).obj
        ((SheafOfModules.toSheaf Z.ringCatSheaf).obj G) where
  hom :=
    Functor.RightDerived.exactSquareApp
      (SheafOfModules.toSheaf Z.ringCatSheaf ⋙
        siteAbelianSectionsFunctor (Opens.grothendieckTopology Z.carrier) U)
      (siteAbelianSectionsFunctor (Opens.grothendieckTopology Z.carrier) U)
      (SheafOfModules.toSheaf Z.ringCatSheaf) (𝟭 AddCommGrpCat.{u})
      (Functor.rightUnitor
        (SheafOfModules.toSheaf Z.ringCatSheaf ⋙
          siteAbelianSectionsFunctor (Opens.grothendieckTopology Z.carrier) U)).hom
      p G
  inv := eqToHom (toSheafCompSectionsRightDerived_obj_eq Z U p G).symm
  hom_inv_id := sorry
  inv_hom_id := sorry

variable {X Y : Scheme.{u}}

/-- The completed local ring `𝒪_{Y,y}^∧`. -/
abbrev completedRing (y : Y) : Type u :=
  AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)

/-- Neighbourhood schemes inherit Ext-groups of abelian sheaves. -/
instance hasExt_scheme (f : X ⟶ Y) (y : Y) (n : ℕ) :
    HasExt (Sheaf (Opens.grothendieckTopology (scheme f y n).carrier) AddCommGrpCat.{u}) :=
  sorry

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

/-- Degree-`p` cohomology `H^p(X_{n+1}, ℱ_{n+1})` as a module over `𝒪_{Y,y} ⧸ m_y^{n+1}`. -/
abbrev homCohomology (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    ModuleCat (quotientRing y n) :=
  cohomology (toSpec f y n) (sheaf f F y n) p

/-- Neighbourhood cohomology is affine-base cohomology of `ℱ_{n+1}` along `toSpec`. -/
theorem homCohomology_eq (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    homCohomology f F y p n = cohomology (toSpec f y n) (sheaf f F y n) p :=
  sorry

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

/-- The spectrum morphism `Spec(𝒪_{Y,y} ⧸ m_y^{n+1}) ⟶ Spec(𝒪_{Y,y} ⧸ m_y^{n+2})`. -/
def transitionSpec (y : Y) (n : ℕ) : quotientSpec y n ⟶ quotientSpec y (n + 1) :=
  Spec.map (CommRingCat.ofHom (quotientStep y n))

/-- `transitionSpec` is `Spec.map` of `quotientStep`. -/
theorem transitionSpec_eq (y : Y) (n : ℕ) :
    transitionSpec y n = Spec.map (CommRingCat.ofHom (quotientStep y n)) :=
  sorry

/-- Global-sections maps of successive structure morphisms commute with `quotientStep`. -/
theorem globalSectionsMap_comp_quotientStep (f : X ⟶ Y) (y : Y) (n : ℕ) :
    (globalSectionsMap (toSpec f y n)).comp (quotientStep y n) =
      (sectionsMapAlong (schemeTransition f y n) ⊤ ⊤ le_top).comp
        (globalSectionsMap (toSpec f y (n + 1))) :=
  sorry

/-- Forgetting the `𝒪_{Y,y} ⧸ m_y^{n+1}`-action on neighbourhood cohomology recovers the
forgotten `Γ(X_{n+1}, ⊤)`-module structure. -/
theorem homCohomology_forget (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (forget₂ (ModuleCat (quotientRing y n)) AddCommGrpCat.{u}).obj
        (homCohomology f F y p n) =
      (forget₂ (ModuleCat Γ(scheme f y n, ⊤)) AddCommGrpCat.{u}).obj
        (Scheme.Modules.cohomology (sheaf f F y n) p) :=
  sorry

/-- Canonical isomorphism between forgotten affine-base neighbourhood cohomology and Ext
cohomology of the underlying additive sheaf. This is not an equality: `Hom.cohomology` is
right-derived module sections, while `RingedSpace.moduleCohomology` is Ext `H'`. -/
def homCohomologySheafIso (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (forget₂ (ModuleCat (quotientRing y n)) AddCommGrpCat.{u}).obj
        (homCohomology f F y p n) ≅
      RingedSpace.moduleCohomology (sheaf f F y n) p where
  hom :=
    eqToHom (homCohomology_forget f F y p n) ≫
      (Functor.RightDerived.postcompIso
          (RingedSpace.moduleSectionsEvaluationFunctor
            (scheme f y n).toRingedSpace ⊤)
          (forget₂ (ModuleCat Γ(scheme f y n, ⊤)) AddCommGrpCat.{u}) p).inv.app
        (sheaf f F y n) ≫
      (CategoryTheory.NatIso.rightDerived
          (moduleSectionsAsAbelianIso (scheme f y n) ⊤) p).hom.app
        (sheaf f F y n) ≫
      (toSheafCompSectionsRightDerivedIso (scheme f y n) ⊤ p (sheaf f F y n)).hom ≫
      (SiteAbelianSectionsDerived.HPrime.rightDerivedSectionsIso
          (Opens.grothendieckTopology (scheme f y n).carrier)
          (⊤ : Opens (scheme f y n)) p).inv.app
        ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
          (sheaf f F y n)) ≫
      eqToHom
        (Sheaf.cohomologyAtObjectFunctor_obj
          (Opens.grothendieckTopology (scheme f y n).carrier)
          (⊤ : Opens (scheme f y n)) p
          ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
            (sheaf f F y n)))
  inv :=
    eqToHom
        (Sheaf.cohomologyAtObjectFunctor_obj
          (Opens.grothendieckTopology (scheme f y n).carrier)
          (⊤ : Opens (scheme f y n)) p
          ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
            (sheaf f F y n))).symm ≫
      (SiteAbelianSectionsDerived.HPrime.rightDerivedSectionsIso
          (Opens.grothendieckTopology (scheme f y n).carrier)
          (⊤ : Opens (scheme f y n)) p).hom.app
        ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj
          (sheaf f F y n)) ≫
      (toSheafCompSectionsRightDerivedIso (scheme f y n) ⊤ p (sheaf f F y n)).inv ≫
      (CategoryTheory.NatIso.rightDerived
          (moduleSectionsAsAbelianIso (scheme f y n) ⊤) p).inv.app
        (sheaf f F y n) ≫
      (Functor.RightDerived.postcompIso
          (RingedSpace.moduleSectionsEvaluationFunctor
            (scheme f y n).toRingedSpace ⊤)
          (forget₂ (ModuleCat Γ(scheme f y n, ⊤)) AddCommGrpCat.{u}) p).hom.app
        (sheaf f F y n) ≫
      eqToHom (homCohomology_forget f F y p n).symm
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Forgetful comparison from affine-base neighbourhood cohomology to abelian sheaf cohomology. -/
def homCohomologyToSheaf (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    (forget₂ (ModuleCat (quotientRing y n)) AddCommGrpCat.{u}).obj
        (homCohomology f F y p n) ⟶
      RingedSpace.moduleCohomology (sheaf f F y n) p :=
  (homCohomologySheafIso f F y p n).hom

/-- Inverse forgetful comparison from abelian sheaf cohomology to affine-base neighbourhood
cohomology. -/
def sheafToHomCohomology (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    RingedSpace.moduleCohomology (sheaf f F y n) p ⟶
      (forget₂ (ModuleCat (quotientRing y n)) AddCommGrpCat.{u}).obj
        (homCohomology f F y p n) :=
  (homCohomologySheafIso f F y p n).inv

/-- The underlying additive sheaf of a module pushforward is the topological
pushforward of the underlying additive sheaf. -/
def modulePushforwardToSheafIso {X Y : Scheme.{u}} (g : X ⟶ Y) (F : X.Modules) :
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

/-- Functorial form of `modulePushforwardToSheafIso`. -/
def modulePushforwardToSheafNatIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
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
      RingedSpace.moduleCohomology (sheaf f F y n) p :=
  RingedSpace.moduleCohomologyMap (sheafTransitionUnit f F y n) p ≫
    CategoryTheory.Sheaf.cohomologyMap
      (modulePushforwardToSheafIso (schemeTransition f y n) (sheaf f F y n)).hom p ⊤ ≫
    CategoryTheory.Sheaf.pushforwardCohomologyMap
      (schemeTransition f y n).base
      ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj (sheaf f F y n))
      p ⊤ ≫
    eqToHom (pushforwardCohomologyMap_top_eq f F y p n)

/-- `sheafCohomologyStep` is the unit map on cohomology followed by the direct-image
comparison. -/
theorem sheafCohomologyStep_eq (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    sheafCohomologyStep f F y p n =
      RingedSpace.moduleCohomologyMap (sheafTransitionUnit f F y n) p ≫
        CategoryTheory.Sheaf.cohomologyMap
          (modulePushforwardToSheafIso (schemeTransition f y n) (sheaf f F y n)).hom
          p ⊤ ≫
        CategoryTheory.Sheaf.pushforwardCohomologyMap
          (schemeTransition f y n).base
          ((SheafOfModules.toSheaf (scheme f y n).ringCatSheaf).obj (sheaf f F y n))
          p ⊤ ≫
        eqToHom (pushforwardCohomologyMap_top_eq f F y p n) :=
  sorry

/-- Underlying function of successor restriction of neighbourhood cohomology. -/
def homCohomologyStepFun (f : X ⟶ Y) (F : X.Modules) (y : Y) (p n : ℕ) :
    homCohomology f F y p (n + 1) → homCohomology f F y p n :=
  fun x ↦
    (homCohomologySheafIso f F y p n).inv.hom
      ((sheafCohomologyStep f F y p n).hom
        ((homCohomologySheafIso f F y p (n + 1)).hom.hom x))

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

end FiberNeighbourhood
end AlgebraicGeometry.Scheme.Hom
