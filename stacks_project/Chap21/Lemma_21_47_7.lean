/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Tensor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.47.7

Perfectness under the canonical structure-sheaf derived tensor product is owned in
`RingedSite.Hom.ModuleDerived`; the chapter file is only the tagged source-facing entry.
-/

open CategoryTheory RingedSite.Hom
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

-- Local instance justification (defeq pin): use the standard derived category and canonical
-- totalization of the structure-sheaf module tensor, matching the shared owner.
attribute [local instance] HasDerivedCategory.standard
  RingedSite.Hom.moduleCat_hasDerivedCategory
  SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable {O : Sheaf J CommRingCat.{w}} [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : RingedSite.ofCommRingSheaf J O,
  HasWeakSheafify ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology
    AddCommGrpCat.{w}]
variable [∀ U : RingedSite.ofCommRingSheaf J O,
  ((RingedSite.ofCommRingSheaf J O).localization U).siteTopology.WEqualsLocallyBijective
    AddCommGrpCat.{w}]
variable [DerivedCategory.DerivedTensor.Right.Has
  (C := SheafOfModules.RingedSite.ringedSiteModuleCategory.{u, v, w, w} J O)]

/- Lemma 21.47.7 (09JB): the derived tensor product of two perfect objects of `D(𝒪_X)` is
perfect. -/
@[stacks 09JB]
#check (RingedSite.Hom.ModuleDerived.IsPerfect.tensor :
  ∀ {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)},
    K.IsPerfect → L.IsPerfect → RingedSite.Hom.ModuleDerived.IsPerfect (K ⊗ᴸ L))

end
