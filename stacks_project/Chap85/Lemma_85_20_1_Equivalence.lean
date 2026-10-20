module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization
public import ReasLib.CategoryTheory.Limits.Over.FiniteLimits
public import stacks_project.Chap85.Lemma_85_18_1_Equivalence
public import stacks_project.Chap85.Lemma_85_19_1_Slice

/-!
# Module descent for a hypercovering of an object

A hypercovering of an object `U` of a ringed site is a site-level hypercovering of
the terminal presheaf on `C / U`. Instantiating module descent on the localized
ringed site yields an equivalence between `O_U`-modules and cartesian `O`-modules
on `((C / K)_total, O)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Functor
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Hypercovering

open CategoryTheory.Hypercovering (toSliceTerminal)
open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

section Terminal

open Localization.AtSimplicialSR

variable (Y : RingedSite.{u, v, w})
variable [h_eq : HasEqualizers Y.carrier] [h_pb : HasPullbacks Y.carrier]
include h_eq h_pb
variable (L : HypercoveringOf.Terminal.{ι} Y.siteTopology)
variable [UnivLE.{max ι u v, w}]
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

/-- Module descent for a site-level hypercovering of the terminal presheaf, with the
ambient ringed site explicit. -/
def cartesianEquivalence_terminal :
    SheafOfModules.{w} Y.structureSheaf ≌ Cartesian L.simplicial :=
  Localization.AtSimplicialSR.cartesianEquivalence L

/-- The forward functor of `cartesianEquivalence_terminal` is `a^*` corestricted to
cartesian `O`-modules. -/
def cartesianFunctor_terminal :
    SheafOfModules.{w} Y.structureSheaf ⥤ Cartesian L.simplicial :=
  cartesianFunctor L

/-- The inverse functor of `cartesianEquivalence_terminal` is `a_*` on cartesian
`O`-modules. -/
def cartesianInverse_terminal :
    Cartesian L.simplicial ⥤ SheafOfModules.{w} Y.structureSheaf :=
  cartesianInverse L

/-- An `O`-module on `((C / K)_total, O)` lies in the essential image of `a^*` if and only
if it is cartesian. -/
theorem mem_essImage_iff_isCartesian_terminal
    (G : SheafOfModules.{w} (ringSheaf L.simplicial)) :
    (modulePullback L.simplicial).essImage G ↔ IsCartesian L.simplicial G :=
  sorry

/-- Inverse image `a^*` along a site-level hypercovering is full. -/
instance modulePullback_full : (modulePullback L.simplicial).Full :=
  sorry

/-- Inverse image `a^*` along a site-level hypercovering is faithful. -/
instance modulePullback_faithful : (modulePullback L.simplicial).Faithful :=
  sorry

/-- Inverse image `a^*` along a site-level hypercovering is fully faithful. -/
def modulePullback_fullyFaithful : (modulePullback L.simplicial).FullyFaithful :=
  FullyFaithful.ofFullyFaithful _

/-- The structure sheaf `O` on `((C / L)_total)`, with the ambient ringed site explicit. -/
abbrev ringSheaf_terminal := ringSheaf L.simplicial

/-- Inverse image `a^*` of modules, with the ambient ringed site explicit. -/
abbrev modulePullback_terminal := modulePullback L.simplicial

/-- The cartesian predicate on `O`-modules, with the ambient ringed site explicit. -/
abbrev IsCartesian_terminal (G : SheafOfModules.{w} (ringSheaf L.simplicial)) : Prop :=
  IsCartesian L.simplicial G

/-- Right-adjointness of restriction of scalars along the ringed augmentation `a`. -/
abbrev toAmbientRestrictScalarsAdjoint :=
  (SheafOfModules.restrictScalars.{w} (toAmbient L.simplicial).structureMap).IsRightAdjoint

/-- Right-adjointness of restriction of scalars along each stage inclusion `g_n`. -/
abbrev stageInclRestrictScalarsAdjoint :=
  ∀ n : SimplexCategory,
    (SheafOfModules.restrictScalars.{w}
      (stageIncl L.simplicial n).structureMap).IsRightAdjoint

/-- Right-adjointness of restriction of scalars along each stage map `f_φ`. -/
abbrev stageMapRestrictScalarsAdjoint :=
  ∀ {m n : SimplexCategory} (φ : m ⟶ n),
    (SheafOfModules.restrictScalars.{w}
      (stageMap L.simplicial φ).structureMap).IsRightAdjoint

end Terminal

variable {X : RingedSite.{u, v, w}}
variable [HasPullbacks X.carrier]
variable (U : X) (K : CategoryTheory.Hypercovering.{ι} X.siteTopology U)
variable [UnivLE.{max ι u v, w}]
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

/-- Inverse image along the ringed augmentation of a hypercovering of an object
implements an equivalence between `O_U`-modules and cartesian `O`-modules, with
quasi-inverse the direct image. -/
def cartesianEquivalence :=
  cartesianEquivalence_terminal (X.localization U) (toSliceTerminal X.siteTopology U K)

/-- The forward functor of `cartesianEquivalence` is `a^*` corestricted to cartesian
`O`-modules. -/
theorem cartesianEquivalence_functor :
    (cartesianEquivalence U K).functor =
      cartesianFunctor_terminal (X.localization U) (toSliceTerminal X.siteTopology U K) :=
  sorry

/-- The inverse functor of `cartesianEquivalence` is `a_*` on cartesian `O`-modules. -/
theorem cartesianEquivalence_inverse :
    (cartesianEquivalence U K).inverse =
      cartesianInverse_terminal (X.localization U) (toSliceTerminal X.siteTopology U K) :=
  sorry

/-- An `O`-module on `((C / K)_total, O)` lies in the essential image of `a^*` if and only
if it is cartesian. -/
theorem mem_essImage_iff_isCartesian
    (G : SheafOfModules.{w}
      (ringSheaf_terminal (X.localization U) (toSliceTerminal X.siteTopology U K))) :
    (modulePullback_terminal (X.localization U)
      (toSliceTerminal X.siteTopology U K)).essImage G ↔
      IsCartesian_terminal (X.localization U)
        (toSliceTerminal X.siteTopology U K) G :=
  sorry

end RingedSite.Hypercovering
