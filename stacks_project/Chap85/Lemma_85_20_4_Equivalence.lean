/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
public import stacks_project.Chap85.Lemma_85_18_4_Equivalence
public import stacks_project.Chap85.Lemma_85_20_1_Equivalence

/-!
# Bounded-below cartesian derived equivalence of a hypercovering of an object

A hypercovering of an object `U` of a ringed site is a site-level hypercovering of
the terminal presheaf on `C / U`. Instantiating Lemma 85.18.4 on the localized
ringed site yields an equivalence `D⁺(O_U) ≌ D_A⁺(O)` with quasi-inverse `Ra_*`,
where `A` is the weak Serre subcategory of cartesian `O`-modules on
`((C / K)_total, O)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ObjectProperty
open Functor
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Hypercovering

open CategoryTheory.Hypercovering (toSliceTerminal)
open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

-- Local instance justification (defeq pin): `Hom.moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `Plus.ι` and `La^*`/`Ra_*` must share that same derived-category instance.
attribute [local instance] Hom.moduleCat_hasDerivedCategory

section Terminal

open Localization.AtSimplicialSR

variable (Y : RingedSite.{u, v, w})
variable [h_eq : HasEqualizers Y.carrier] [h_pbY : HasPullbacks Y.carrier]
include h_eq h_pbY
variable (L : HypercoveringOf.Terminal.{ι} Y.siteTopology)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (overSiteTotalTopology Y.siteTopology L.simplicial) (Type w)]
variable [HasWeakSheafify (overSiteTotalTopology Y.siteTopology L.simplicial) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify (overTopology Y.siteTopology (L.simplicial.obj (op n))) (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify (overTopology Y.siteTopology (L.simplicial.obj (op n))) (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram L.simplicial))ᵒᵖ ⥤ Type w,
    (totalForget L.simplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory, ∀ P : (OverSite (L.simplicial.obj (op n)))ᵒᵖ ⥤ Type w,
    (Grothendieck.ι (overSiteDiagram L.simplicial) (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (L.simplicial.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (L.simplicial.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology Y.siteTopology L.simplicial).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [Y.siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology Y.siteTopology (L.simplicial.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
variable [(SheafOfModules.restrictScalars.{w}
    (toAmbient L.simplicial).structureMap).IsRightAdjoint]
variable [∀ n : SimplexCategory,
    (SheafOfModules.restrictScalars.{w}
      (stageIncl L.simplicial n).structureMap).IsRightAdjoint]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (stageMap L.simplicial φ).structureMap).IsRightAdjoint]
variable [ToposHom.HasModulePullbackDerived (toAmbient L.simplicial)]
variable [ToposHom.HasModulePushforwardDerived (toAmbient L.simplicial)]
variable [ToposHom.HasModuleDerivedAdjunction (toAmbient L.simplicial)]

/-- The cartesian object property of `O`-modules, with the ambient ringed site
explicit. -/
abbrev cartesianProperty_terminal :=
  cartesianProperty L.simplicial

/-- Cartesian `O`-modules on `((C / L)_total, O)` form a weak Serre subcategory,
with the ambient ringed site explicit. -/
instance cartesianProperty_isWeakSerreClass_terminal :
    IsWeakSerreClass (cartesianProperty_terminal Y L) :=
  Localization.AtSimplicialSR.cartesianProperty_isWeakSerreClass L

/-- The bounded-below cohomology-in property cut out by cartesian `O`-modules,
with the ambient ringed site explicit. -/
abbrev cartesianPlusProperty_terminal :=
  cartesianPlusProperty L

/-- Bounded-below derived objects with cartesian cohomology `D_A⁺(O)`, with the
ambient ringed site explicit. -/
abbrev CartesianPlus_terminal :=
  CartesianPlus L

/-- The functor `La^*` corestricted to `D⁺(O_Y) ⥤ D_A⁺(O)`, with the ambient
ringed site explicit. -/
def plusCartesianFunctor_terminal :
    DerivedCategory.Plus (ModuleCat.{w} Y) ⥤ CartesianPlus_terminal Y L :=
  plusCartesianFunctor L

/-- The functor `Ra_*` restricted from `D_A⁺(O)` to `D⁺(O_Y)`, with the ambient
ringed site explicit. -/
def plusCartesianInverse_terminal :
    CartesianPlus_terminal Y L ⥤ DerivedCategory.Plus (ModuleCat.{w} Y) :=
  plusCartesianInverse L

/-- `La^*` implements an equivalence `D⁺(O_Y) ≌ D_A⁺(O)` with quasi-inverse `Ra_*`,
with the ambient ringed site explicit. -/
def plusCartesianEquivalence_terminal :
    DerivedCategory.Plus (ModuleCat.{w} Y) ≌ CartesianPlus_terminal Y L :=
  Localization.AtSimplicialSR.plusCartesianEquivalence L

end Terminal

variable {X : RingedSite.{u, v, w}}
variable [HasPullbacks X.carrier]
variable (U : X) (K : CategoryTheory.Hypercovering.{ι} X.siteTopology U)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
variable [HasSheafify
    (overSiteTotalTopology (X.localization U).siteTopology K.toSimplicialObject) (Type w)]
variable [HasWeakSheafify
    (overSiteTotalTopology (X.localization U).siteTopology K.toSimplicialObject) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify
      (overTopology (X.localization U).siteTopology (K.toSimplicialObject.obj (op n)))
      (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify
      (overTopology (X.localization U).siteTopology (K.toSimplicialObject.obj (op n)))
      (Type w)]
variable [∀ P : (Grothendieck (overSiteDiagram K.toSimplicialObject))ᵒᵖ ⥤ Type w,
    (totalForget K.toSimplicialObject).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory,
    ∀ P : (OverSite (K.toSimplicialObject.obj (op n)))ᵒᵖ ⥤ Type w,
      (Grothendieck.ι (overSiteDiagram K.toSimplicialObject) (op n)).op.HasPointwiseRightKanExtension
        P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.toSimplicialObject.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap (K.toSimplicialObject.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [(overSiteTotalTopology (X.localization U).siteTopology
    K.toSimplicialObject).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(X.localization U).siteTopology.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology (X.localization U).siteTopology
      (K.toSimplicialObject.obj (op n))).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [toAmbientRestrictScalarsAdjoint (X.localization U)
    (toSliceTerminal X.siteTopology U K)]
variable [stageInclRestrictScalarsAdjoint (X.localization U)
    (toSliceTerminal X.siteTopology U K)]
variable [stageMapRestrictScalarsAdjoint (X.localization U)
    (toSliceTerminal X.siteTopology U K)]
variable [ToposHom.HasModulePullbackDerived
    (Localization.AtSimplicialSR.toAmbient.{ι, max u v, v, w}
      (toSliceTerminal X.siteTopology U K).simplicial :
      ToposHom _ (X.localization U))]
variable [ToposHom.HasModulePushforwardDerived
    (Localization.AtSimplicialSR.toAmbient.{ι, max u v, v, w}
      (toSliceTerminal X.siteTopology U K).simplicial :
      ToposHom _ (X.localization U))]
variable [ToposHom.HasModuleDerivedAdjunction
    (Localization.AtSimplicialSR.toAmbient.{ι, max u v, v, w}
      (toSliceTerminal X.siteTopology U K).simplicial :
      ToposHom _ (X.localization U))]

/-- The bounded-below cohomology-in property cut out by cartesian `O`-modules on
`((C / K)_total, O)`. -/
abbrev cartesianPlusProperty :=
  cartesianPlusProperty_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)

/-- Bounded-below derived objects with cartesian cohomology: `D_A⁺(O)` for a
hypercovering of an object. -/
abbrev CartesianPlus :=
  CartesianPlus_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)

/-- The functor `La^*` corestricted to `D⁺(O_U) ⥤ D_A⁺(O)`. -/
abbrev plusCartesianFunctor :=
  plusCartesianFunctor_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)

/-- The functor `Ra_*` restricted from `D_A⁺(O)` to `D⁺(O_U)`. -/
abbrev plusCartesianInverse :=
  plusCartesianInverse_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)

/-- Inverse image along the ringed augmentation of a hypercovering of an object
implements an equivalence `D⁺(O_U) ≌ D_A⁺(O)`, with quasi-inverse `Ra_*`. -/
def plusCartesianEquivalence :=
  plusCartesianEquivalence_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)

/-- Cartesian `O`-modules on `((C / K)_total, O)` form a weak Serre subcategory. -/
instance cartesianProperty_isWeakSerreClass :
    IsWeakSerreClass
      (cartesianProperty_terminal (X.localization U)
        (toSliceTerminal X.siteTopology U K)) :=
  cartesianProperty_isWeakSerreClass_terminal (X.localization U)
    (toSliceTerminal X.siteTopology U K)

/-- The forward functor of `plusCartesianEquivalence` is `La^*` corestricted to
`D_A⁺(O)`. -/
theorem plusCartesianEquivalence_functor :
    (plusCartesianEquivalence U K).functor = plusCartesianFunctor U K :=
  sorry

/-- The inverse functor of `plusCartesianEquivalence` is `Ra_*` restricted from
`D_A⁺(O)`. -/
theorem plusCartesianEquivalence_inverse :
    (plusCartesianEquivalence U K).inverse = plusCartesianInverse U K :=
  sorry

/-- The corestricted functor `La^* : D⁺(O_U) ⥤ D_A⁺(O)` is an equivalence. -/
instance plusCartesianFunctor_isEquivalence :
    (plusCartesianFunctor U K).IsEquivalence :=
  Equivalence.isEquivalence_functor (plusCartesianEquivalence U K)

end RingedSite.Hypercovering
