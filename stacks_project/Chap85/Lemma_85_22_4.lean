/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Hypercovering.Augmented
public import ReasLib.AlgebraicGeometry.RingedSite.Hypercovering.CartesianDerivedEquivalence

/-!
# Lemma 85.22.4

Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a
sheaf of rings. Let `U` be a hypercovering of `X` in `C`. Let `A ⊂ Mod(O)`
denote the weak Serre subcategory of cartesian `O`-modules. Then the functor
`La^*` defines an equivalence `D⁺(O_X) ≌ D_A⁺(O)` with quasi-inverse `Ra_*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite
open CategoryTheory.Hypercovering (toSliceTerminal)
open RingedSite.Hypercovering
  (plusCartesianFunctor plusCartesianInverse
    toAmbientRestrictScalarsAdjoint
    stageInclRestrictScalarsAdjoint stageMapRestrictScalarsAdjoint)
open SemiRepresentableFamily
  (OverSite overTopology overSiteDiagram overSiteTotalTopology totalForget overMap)
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe ι u v w

namespace CategoryTheory.SimplicialObject.Augmented

-- Local instance justification (defeq pin): `Hom.moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `Plus.ι` and `La^*`/`Ra_*` must share that same derived-category instance.
attribute [local instance] Hom.moduleCat_hasDerivedCategory

variable {X : RingedSite.{u, v, w}}
variable [h_pb : HasPullbacks X.carrier]
include h_pb
variable (A : SimplicialObject.Augmented X.carrier)
variable (hA : A.IsHypercovering X.siteTopology)
variable [UnivLE.{max ι u v, w}]
variable [UnivLE.{max u v, w}]
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
variable [ToposHom.HasModulePullbackDerived
    (Localization.AtSimplicialSR.toAmbient.{ι, max u v, v, w}
      (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA)).simplicial :
      ToposHom _ (X.localization A.right))]
variable [ToposHom.HasModulePushforwardDerived
    (Localization.AtSimplicialSR.toAmbient.{ι, max u v, v, w}
      (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA)).simplicial :
      ToposHom _ (X.localization A.right))]
variable [ToposHom.HasModuleDerivedAdjunction
    (Localization.AtSimplicialSR.toAmbient.{ι, max u v, v, w}
      (toSliceTerminal X.siteTopology A.right (toHypercovering.{ι} A hA)).simplicial :
      ToposHom _ (X.localization A.right))]

/- Lemma 85.22.4
Let `C` be a site with fibre products and `X` an object of `C`. Let `O_C` be a sheaf of
rings. Let `U` be a hypercovering of `X` in `C`. Let `A ⊂ Mod(O)` denote the weak Serre
subcategory of cartesian `O`-modules. Then the functor `La^*` defines an equivalence
`D⁺(O_X) ≌ D_A⁺(O)` with quasi-inverse `Ra_*`.

Here `U → X` is the augmented simplicial object `A` of the site, `O_X` is the structure
sheaf of `X.localization A.right`, `O` is the structure sheaf of the total ringed site of
the hypercovering `toHypercovering A hA`, `A` is the object property `cartesianProperty`
of cartesian `O`-modules, `La^*` is `plusCartesianFunctor`, and `Ra_*` is
`plusCartesianInverse`. -/
@[stacks 0DAE] #check
  (RingedSite.Hypercovering.modulePlusCartesianEquivalence.{ι, u, v, w}
    A.right (toHypercovering.{ι} A hA) :
    DerivedCategory.Plus (ModuleCat.{w} (X.localization A.right)) ≌
      RingedSite.Hypercovering.CartesianPlus A.right (toHypercovering.{ι} A hA))

/- The forward functor of `modulePlusCartesianEquivalence` is `La^*` corestricted to
`D_A⁺(O)`. -/
#check
  (RingedSite.Hypercovering.modulePlusCartesianEquivalence_functor.{ι, u, v, w}
    A.right (toHypercovering.{ι} A hA) :
    (RingedSite.Hypercovering.modulePlusCartesianEquivalence.{ι, u, v, w}
      A.right (toHypercovering.{ι} A hA)).functor =
      plusCartesianFunctor.{ι, u, v, w} A.right (toHypercovering.{ι} A hA))

/- The inverse functor of `modulePlusCartesianEquivalence` is `Ra_*` restricted from
`D_A⁺(O)`. -/
#check
  (RingedSite.Hypercovering.modulePlusCartesianEquivalence_inverse.{ι, u, v, w}
    A.right (toHypercovering.{ι} A hA) :
    (RingedSite.Hypercovering.modulePlusCartesianEquivalence.{ι, u, v, w}
      A.right (toHypercovering.{ι} A hA)).inverse =
      plusCartesianInverse.{ι, u, v, w} A.right (toHypercovering.{ι} A hA))

end CategoryTheory.SimplicialObject.Augmented
