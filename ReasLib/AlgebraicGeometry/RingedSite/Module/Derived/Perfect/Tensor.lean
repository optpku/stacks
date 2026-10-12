/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor

/-!
# Perfect derived tensor products on ringed sites

This module records stability of perfect derived module sheaves under the abstract fixed-right
derived tensor construction.  The statement depends on the derivability interface rather than a
chosen K-flat model, so construction details remain outside downstream APIs.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived)
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

set_option checkBinderAnnotations false

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): generic derived-tensor APIs must align with the canonical RingedSite.Hom.ModuleDerived presentation.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory

section

variable {X : RingedSite.{u, v, w}} [UnivLE.{max u v, w}]
variable [∀ U : X,
  HasWeakSheafify (X.localization U).siteTopology AddCommGrpCat.{w}]
variable [∀ U : X,
  (X.localization U).siteTopology.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [MonoidalCategory (ModuleCat.{w} X)] [MonoidalPreadditive (ModuleCat.{w} X)]
variable [∀ (K L : CochainComplex (ModuleCat.{w} X) ℤ),
  HomologicalComplex.HasMapBifunctor K L (curriedTensor (ModuleCat.{w} X)) (up ℤ)]
variable [@CategoryTheory.DerivedCategory.DerivedTensor.Right.Has
  (ModuleCat.{w} X) inferInstance inferInstance
  (RingedSite.Hom.moduleCat_hasDerivedCategory X)
  inferInstance inferInstance inferInstance]

/-- The derived tensor product of two perfect objects of `D(𝒪_X)` is perfect. -/
@[stacks 09JB]
theorem IsPerfect.tensor
    {K L : ModuleDerived.{w} X} (hK : K.IsPerfect) (hL : L.IsPerfect) :
    IsPerfect (X := X)
      (@DerivedCategory.DerivedTensor.Right.obj
        (ModuleCat.{w} X) inferInstance inferInstance
        (RingedSite.Hom.moduleCat_hasDerivedCategory X)
        inferInstance inferInstance inferInstance K L inferInstance) := sorry

end

end RingedSite.Hom.ModuleDerived
