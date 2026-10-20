/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_18_1_Cartesian
public import stacks_project.Chap85.Lemma_85_18_1_Equivalence

/-!
# Lemma 85.18.1

Let `C` be a site with equalizers and fibre products, let `O_C` be a sheaf of rings, and let
`K` be a hypercovering. Then `a^* : Mod(O_C) ⥤ Mod(O)` is fully faithful with essential image
the cartesian `O`-modules, and `a_*` provides the quasi-inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace RingedSite.Localization.AtSimplicialSR

open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)

variable {X : RingedSite.{u, v, w}}
variable [HasEqualizers X.carrier] [HasPullbacks X.carrier]
variable (K : HypercoveringOf.Terminal.{ι} X.siteTopology)
variable [UnivLE.{max ι u v, w}]
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

/-- Lemma 85.18.1
Let `C` be a site with equalizers and fibre products. Let `O_C` be a sheaf of rings. Let `K`
be a hypercovering. With notation as above, `a^* : Mod(O_C) ⥤ Mod(O)` is fully faithful with
essential image the cartesian `O`-modules. The functor `a_*` provides the quasi-inverse. -/
@[stacks 0D9Z]
def moduleCartesianEquivalence :
    SheafOfModules.{w} X.structureSheaf ≌ Cartesian K.simplicial :=
  cartesianEquivalence K

/-- The forward functor of `moduleCartesianEquivalence` is `a^*` corestricted to cartesian
`O`-modules. -/
theorem moduleCartesianEquivalence_functor :
    (moduleCartesianEquivalence K).functor = cartesianFunctor K :=
  sorry

/-- The inverse functor of `moduleCartesianEquivalence` is `a_*` on cartesian `O`-modules. -/
theorem moduleCartesianEquivalence_inverse :
    (moduleCartesianEquivalence K).inverse = cartesianInverse K :=
  sorry

/-- An `O`-module on `((C / K)_total, O)` lies in the essential image of `a^*` if and only
if it is cartesian. -/
theorem module_mem_essImage_iff_isCartesian
    (G : SheafOfModules.{w} (ringSheaf K.simplicial)) :
    (modulePullback K.simplicial).essImage G ↔ IsCartesian K.simplicial G :=
  sorry

end RingedSite.Localization.AtSimplicialSR
