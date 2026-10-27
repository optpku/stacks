/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import ReasLib.AlgebraicGeometry.RingedSite.Hypercovering.ModuleDescent

/-!
# Lemma 85.22.1

Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a
sheaf of rings. Let `U` be a hypercovering of `X` in `C`. Then
`a^* : Mod(O_X) ⥤ Mod(O)` is fully faithful with essential image the cartesian
`O`-modules, and `a_*` provides the quasi-inverse.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open CategoryTheory.Hypercovering (toSliceTerminal)
open RingedSite.Hypercovering
  (cartesianFunctor_terminal cartesianInverse_terminal modulePullback_terminal
    IsCartesian_terminal ringSheaf_terminal toAmbientRestrictScalarsAdjoint
    stageInclRestrictScalarsAdjoint stageMapRestrictScalarsAdjoint)
open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace CategoryTheory.SimplicialObject.Augmented

variable {X : RingedSite.{u, v, w}}
variable [HasPullbacks X.carrier]
variable (A : SimplicialObject.Augmented X.carrier)
variable (hA : A.IsHypercovering X.siteTopology)
variable [UnivLE.{max ι u v, w}]
variable [HasSheafify
    (overSiteTotalTopology (X.localization A.right).siteTopology
      (toHypercovering.{ι} A hA).toSimplicialObject) (Type w)]
variable [HasWeakSheafify
    (overSiteTotalTopology (X.localization A.right).siteTopology
      (toHypercovering.{ι} A hA).toSimplicialObject) (Type w)]
variable [∀ n : SimplexCategory,
    HasSheafify
      (overTopology (X.localization A.right).siteTopology
        ((toHypercovering.{ι} A hA).toSimplicialObject.obj (op n)))
      (Type w)]
variable [∀ n : SimplexCategory,
    HasWeakSheafify
      (overTopology (X.localization A.right).siteTopology
        ((toHypercovering.{ι} A hA).toSimplicialObject.obj (op n)))
      (Type w)]
variable [∀ P : (Grothendieck
      (overSiteDiagram (toHypercovering.{ι} A hA).toSimplicialObject))ᵒᵖ ⥤ Type w,
    (totalForget (toHypercovering.{ι} A hA).toSimplicialObject).op.HasPointwiseRightKanExtension P]
variable [∀ n : SimplexCategory,
    ∀ P : (OverSite ((toHypercovering.{ι} A hA).toSimplicialObject.obj (op n)))ᵒᵖ ⥤ Type w,
      (Grothendieck.ι (overSiteDiagram (toHypercovering.{ι} A hA).toSimplicialObject)
          (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite ((toHypercovering.{ι} A hA).toSimplicialObject.obj (op n)))ᵒᵖ ⥤ Type w,
      (overMap ((toHypercovering.{ι} A hA).toSimplicialObject.map φ.op)).op.HasPointwiseRightKanExtension
        P]
variable [(overSiteTotalTopology (X.localization A.right).siteTopology
    (toHypercovering.{ι} A hA).toSimplicialObject).HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [(X.localization A.right).siteTopology.HasSheafCompose
    (CategoryTheory.forget RingCat.{w})]
variable [∀ n : SimplexCategory,
    (overTopology (X.localization A.right).siteTopology
      ((toHypercovering.{ι} A hA).toSimplicialObject.obj (op n))).HasSheafCompose
      (CategoryTheory.forget RingCat.{w})]
variable [toAmbientRestrictScalarsAdjoint (X.localization A.right)
    (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA))]
variable [stageInclRestrictScalarsAdjoint (X.localization A.right)
    (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA))]
variable [stageMapRestrictScalarsAdjoint (X.localization A.right)
    (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA))]

/- Lemma 85.22.1
Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a sheaf of
rings. Let `U` be a hypercovering of `X` in `C`. With notation as above,
`a^* : Mod(O_X) ⥤ Mod(O)` is fully faithful with essential image the cartesian
`O`-modules. The functor `a_*` provides the quasi-inverse. -/
@[stacks 0DAB]
#check (RingedSite.Hypercovering.moduleCartesianEquivalence A.right (toHypercovering.{ι} A hA) :
  SheafOfModules.{w} (X.localization A.right).structureSheaf ≌
    RingedSite.Localization.AtSimplicialSR.Cartesian (X := X.localization A.right)
      (toHypercovering.{ι} A hA).toSimplicialObject)

/- The forward functor of `moduleCartesianEquivalence` is `a^*` corestricted to cartesian
`O`-modules. -/
#check (RingedSite.Hypercovering.moduleCartesianEquivalence_functor A.right
    (toHypercovering.{ι} A hA) :
    (RingedSite.Hypercovering.moduleCartesianEquivalence A.right
      (toHypercovering.{ι} A hA)).functor =
      cartesianFunctor_terminal (X.localization A.right)
        (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA)))

/- The inverse functor of `moduleCartesianEquivalence` is `a_*` on cartesian `O`-modules. -/
#check (RingedSite.Hypercovering.moduleCartesianEquivalence_inverse A.right
    (toHypercovering.{ι} A hA) :
    (RingedSite.Hypercovering.moduleCartesianEquivalence A.right
      (toHypercovering.{ι} A hA)).inverse =
      cartesianInverse_terminal (X.localization A.right)
        (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA)))

/- An `O`-module on `((C / U)_total, O)` lies in the essential image of `a^*` if and only
if it is cartesian. -/
#check (RingedSite.Hypercovering.module_mem_essImage_iff_isCartesian A.right
    (toHypercovering.{ι} A hA) :
    ∀ G : SheafOfModules.{w}
      (ringSheaf_terminal (X.localization A.right)
        (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA))),
    (modulePullback_terminal (X.localization A.right)
      (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA))).essImage G ↔
      IsCartesian_terminal (X.localization A.right)
        (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA)) G)

/- Pullback along the augmentation is fully faithful. -/
#check (RingedSite.Hypercovering.modulePullback_fullyFaithful A.right
    (toHypercovering.{ι} A hA) :
    (modulePullback_terminal (X.localization A.right)
      (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA))).FullyFaithful)

end CategoryTheory.SimplicialObject.Augmented
