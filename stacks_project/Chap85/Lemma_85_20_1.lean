module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_20_1_Equivalence

/-!
# Lemma 85.20.1

Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a
sheaf of rings. Let `K` be a hypercovering of `X`. Then
`a^* : Mod(O_X) ⥤ Mod(O)` is fully faithful with essential image the cartesian
`O`-modules, and `a_*` provides the quasi-inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Hypercovering

open CategoryTheory.Hypercovering (toSliceTerminal)
open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

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

/-- Lemma 85.20.1
Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a sheaf of
rings. Let `K` be a hypercovering of `X`. With notation as above,
`a^* : Mod(O_X) ⥤ Mod(O)` is fully faithful with essential image the cartesian
`O`-modules. The functor `a_*` provides the quasi-inverse. -/
@[stacks 0DA4]
def moduleCartesianEquivalence :=
  cartesianEquivalence U K

/-- The forward functor of `moduleCartesianEquivalence` is `a^*` corestricted to cartesian
`O`-modules. -/
theorem moduleCartesianEquivalence_functor :
    (moduleCartesianEquivalence U K).functor =
      cartesianFunctor_terminal (X.localization U) (toSliceTerminal X.siteTopology U K) :=
  sorry

/-- The inverse functor of `moduleCartesianEquivalence` is `a_*` on cartesian `O`-modules. -/
theorem moduleCartesianEquivalence_inverse :
    (moduleCartesianEquivalence U K).inverse =
      cartesianInverse_terminal (X.localization U) (toSliceTerminal X.siteTopology U K) :=
  sorry

/-- An `O`-module on `((C / K)_total, O)` lies in the essential image of `a^*` if and only
if it is cartesian. -/
theorem module_mem_essImage_iff_isCartesian
    (G : SheafOfModules.{w}
      (ringSheaf_terminal (X.localization U) (toSliceTerminal X.siteTopology U K))) :
    (modulePullback_terminal (X.localization U)
      (toSliceTerminal X.siteTopology U K)).essImage G ↔
      IsCartesian_terminal (X.localization U)
        (toSliceTerminal X.siteTopology U K) G :=
  sorry

end RingedSite.Hypercovering
