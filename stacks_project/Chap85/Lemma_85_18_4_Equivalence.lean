module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.Module.Derived.Adjunction
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction
public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
public import ReasLib.CategoryTheory.Sites.Hypercovering.PresheafTarget.Terminal
public import stacks_project.Chap85.Lemma_85_18_1_Cartesian

/-!
# Bounded-below cartesian derived equivalence of a hypercovering

If `K` is a hypercovering of the terminal presheaf, the derived inverse image `La^*`
implements an equivalence `D⁺(O_C) ≌ D_A⁺(O)` with quasi-inverse `Ra_*`, where `A` is
the weak Serre subcategory of cartesian `O`-modules on `((C / K)_total, O)`.

The maps `La^*` and `Ra_*` are the ToposHom derived module functors of `toAmbient`,
the same maps named `modulePullbackDerived` / `modulePushforwardDerived` in
Lemma 85.18.2.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

-- Local instance justification (defeq pin): `Hom.moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `Plus.ι` and `modulePullbackDerived`/`modulePushforwardDerived` must share that same derived-category instance.
attribute [local instance] Hom.moduleCat_hasDerivedCategory

variable {X : RingedSite.{u, v, w}}
variable [h_eq : HasEqualizers X.carrier] [h_pb : HasPullbacks X.carrier]
include h_eq h_pb
variable (K : HypercoveringOf.Terminal.{ι} X.siteTopology)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)]
variable [HasWeakSheafify (overSiteTotalTopology X.siteTopology K.simplicial) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify (overTopology X.siteTopology (K.simplicial.obj (op n))) (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify (overTopology X.siteTopology (K.simplicial.obj (op n))) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.simplicial))ᵒᵖ ⥤ Type w,
    (totalForget K.simplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory, ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ Type w,
    (Grothendieck.ι (overSiteDiagram K.simplicial) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.simplicial.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology X.siteTopology K.simplicial).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [X.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology X.siteTopology (K.simplicial.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w}
    (toAmbient K.simplicial).structureMap).IsRightAdjoint]
variable [∀ n : SimplexCategory,
    (SheafOfModules.restrictScalars.{w}
      (stageIncl K.simplicial n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (stageMap K.simplicial φ).structureMap).IsRightAdjoint]
variable [ToposHom.HasModulePullbackDerived (toAmbient K.simplicial)]
variable [ToposHom.HasModulePushforwardDerived (toAmbient K.simplicial)]
variable [ToposHom.HasModuleDerivedAdjunction (toAmbient K.simplicial)]

/-- The weak Serre subcategory `A` of cartesian `O`-modules on `((C / K)_total, O)`. -/
instance cartesianProperty_isWeakSerreClass :
    IsWeakSerreClass (cartesianProperty K.simplicial) :=
  sorry

/-- The bounded-below cohomology-in property cut out by cartesian `O`-modules. -/
abbrev cartesianPlusProperty :
    ObjectProperty (DerivedCategory.Plus (ModuleCat.{w} (site K.simplicial))) :=
  DerivedCategory.Plus.cohomologyIn
    (cartesianProperty K.simplicial :
      ObjectProperty (ModuleCat.{w} (site K.simplicial)))

/-- Bounded-below derived objects with cartesian cohomology: `D_A⁺(O)`. -/
abbrev CartesianPlus := (cartesianPlusProperty K).FullSubcategory

/-- `La^*` sends bounded-below `O_C`-modules to bounded-below `O`-modules. -/
theorem modulePullbackDerived_mapsPlus :
    (t.plus : ObjectProperty (Hom.ModuleDerived.{w} X)) ≤
      (t.plus : ObjectProperty (Hom.ModuleDerived.{w} (site K.simplicial))).inverseImage
        (toAmbient K.simplicial).modulePullbackDerived :=
  sorry

/-- Bounded-below derived inverse image `La^*` along a hypercovering. -/
def plusPullback :
    DerivedCategory.Plus (ModuleCat.{w} X) ⥤
      DerivedCategory.Plus (ModuleCat.{w} (site K.simplicial)) :=
  FullSubcategory.restrict (toAmbient K.simplicial).modulePullbackDerived
    (modulePullbackDerived_mapsPlus K)

/-- `La^*` of a bounded-below complex has cartesian cohomology. -/
theorem mapsPullbackDerived_plus
    (E : DerivedCategory.Plus (ModuleCat.{w} X)) :
    cartesianPlusProperty K
      ((plusPullback K).obj E) :=
  sorry

/-- The functor `La^*` corestricted to `D⁺(O_C) ⥤ D_A⁺(O)`. -/
def plusCartesianFunctor :
    DerivedCategory.Plus (ModuleCat.{w} X) ⥤ CartesianPlus K :=
  (cartesianPlusProperty K).lift
    (plusPullback K) (mapsPullbackDerived_plus K)

/-- Forgetting `D_A⁺(O)` recovers `La^*` after the bounded-below inclusion. -/
def plusCartesianFunctor_comp_ι :
    plusCartesianFunctor K ⋙
      (cartesianPlusProperty K).ι ⋙
      DerivedCategory.Plus.ι ≅
    DerivedCategory.Plus.ι ⋙ (toAmbient K.simplicial).modulePullbackDerived :=
  FullSubcategory.restrict.compιIso (toAmbient K.simplicial).modulePullbackDerived
    (modulePullbackDerived_mapsPlus K)

/-- `Ra_*` sends bounded-below complexes with cartesian cohomology to bounded-below
`O_C`-modules. -/
theorem modulePushforwardDerived_mapsPlus :
    cartesianPlusProperty K ≤
      (t.plus : ObjectProperty (Hom.ModuleDerived.{w} X)).inverseImage
        (DerivedCategory.Plus.ι ⋙ (toAmbient K.simplicial).modulePushforwardDerived) :=
  sorry

/-- The functor `Ra_*` restricted from `D_A⁺(O)` to `D⁺(O_C)`. -/
def plusCartesianInverse :
    CartesianPlus K ⥤ DerivedCategory.Plus (ModuleCat.{w} X) :=
  FullSubcategory.restrict
    (DerivedCategory.Plus.ι ⋙ (toAmbient K.simplicial).modulePushforwardDerived)
    (modulePushforwardDerived_mapsPlus K)

/-- Forgetting `D⁺(O_C)` recovers `Ra_*` after the cartesian cohomology inclusion. -/
def plusCartesianInverse_comp_ι :
    plusCartesianInverse K ⋙ DerivedCategory.Plus.ι ≅
      (cartesianPlusProperty K).ι ⋙
        DerivedCategory.Plus.ι ⋙ (toAmbient K.simplicial).modulePushforwardDerived :=
  FullSubcategory.restrict.compιIso
    (DerivedCategory.Plus.ι ⋙ (toAmbient K.simplicial).modulePushforwardDerived)
    (modulePushforwardDerived_mapsPlus K)

/-- The derived unit `E ⟶ Ra_* La^* E` is an isomorphism on bounded-below `O_C`-modules. -/
theorem plusCartesianUnit_app_isIso
    (E : DerivedCategory.Plus (ModuleCat.{w} X)) :
    IsIso ((ToposHom.moduleDerivedAdjunction (toAmbient K.simplicial)).unit.app E.obj) :=
  sorry

/-- The unit isomorphism `𝟭 ≅ La^* ⋙ Ra_*` on `D⁺(O_C)`. -/
def plusCartesianUnitIso :
    𝟭 (DerivedCategory.Plus (ModuleCat.{w} X)) ≅
      plusCartesianFunctor K ⋙ plusCartesianInverse K :=
  NatIso.ofComponents
    (fun E ↦
      t.plus.isoMk
        (@asIso _ _ _ _
          ((ToposHom.moduleDerivedAdjunction (toAmbient K.simplicial)).unit.app E.obj)
          (plusCartesianUnit_app_isIso K E)))
    sorry

/-- The derived counit `La^* Ra_* G ⟶ G` is an isomorphism on `D_A⁺(O)`. -/
theorem plusCartesianCounit_app_isIso (G : CartesianPlus K) :
    IsIso ((ToposHom.moduleDerivedAdjunction (toAmbient K.simplicial)).counit.app
      G.obj.obj) :=
  sorry

/-- The counit isomorphism `Ra_* ⋙ La^* ≅ 𝟭` on `D_A⁺(O)`. -/
def plusCartesianCounitIso :
    plusCartesianInverse K ⋙ plusCartesianFunctor K ≅ 𝟭 (CartesianPlus K) :=
  NatIso.ofComponents
    (fun G ↦
      (cartesianPlusProperty K).isoMk
        (t.plus.isoMk
          (@asIso _ _ _ _
            ((ToposHom.moduleDerivedAdjunction (toAmbient K.simplicial)).counit.app
              G.obj.obj)
            (plusCartesianCounit_app_isIso K G))))
    sorry

/-- `La^*` implements an equivalence `D⁺(O_C) ≌ D_A⁺(O)` with quasi-inverse `Ra_*`. -/
def plusCartesianEquivalence :
    DerivedCategory.Plus (ModuleCat.{w} X) ≌ CartesianPlus K :=
  CategoryTheory.Equivalence.mk (plusCartesianFunctor K) (plusCartesianInverse K)
    (plusCartesianUnitIso K) (plusCartesianCounitIso K)

/-- The forward functor of `plusCartesianEquivalence` is `La^*` corestricted to `D_A⁺`. -/
theorem plusCartesianEquivalence_functor :
    (plusCartesianEquivalence K).functor = plusCartesianFunctor K :=
  sorry

/-- The inverse functor of `plusCartesianEquivalence` is `Ra_*` restricted from `D_A⁺`. -/
theorem plusCartesianEquivalence_inverse :
    (plusCartesianEquivalence K).inverse = plusCartesianInverse K :=
  sorry

end RingedSite.Localization.AtSimplicialSR
