/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.AtiyahTriangle
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open SheafOfModules.RingedSite

universe u

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
variable [UnivLE.{u, u}]
variable [HasSheafify (SimplicialSite.topology J) AddCommGrpCat.{u}]
variable [GrothendieckTopology.WEqualsLocallyBijective
    (SimplicialSite.topology J) AddCommGrpCat.{u}]
variable [GrothendieckTopology.HasSheafCompose (SimplicialSite.topology J)
    (forget₂ CommRingCat.{u} RingCat.{u})]
variable {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B)
variable (F : ringedSiteModuleCategory.{u, u, u, u} J B)

-- Local instance justification (defeq pin): pin the canonical standard derived category of module sheaves.
attribute [local instance] moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): pin the canonical abelian category of module sheaves.
attribute [local instance] moduleCategoryAbelian

variable [DerivedCategory.DerivedTensor.Has (C := ringedSiteModuleCategory.{u, u, u, u} J B)]
variable [DerivedCategory.DerivedTensor.Left.Has (C := ringedSiteModuleCategory.{u, u, u, u} J B)]
variable [DerivedCategory.DerivedTensor.Bifunctor.Has (C := ringedSiteModuleCategory.{u, u, u, u} J B)]

/- Definition 92.19.1: Let C be a site. Let A ⟶ B be a homomorphism of sheaves
of rings. Let F be a sheaf of B-modules. The map F ⟶ (L_{B/A} ⊗^L_B F)⟦1⟧
in 92.19.0.2 is called the Atiyah class of F. This is connectingMap,
equivalently the third arrow of atiyahTriangle. -/
@[stacks 09DI]
#check (SheafOfModules.RingedSite.CotangentComplex.connectingMap φ F :
  (DerivedCategory.singleFunctor (ringedSiteModuleCategory.{u, u, u, u} J B) 0).obj F ⟶
    (SheafOfModules.RingedSite.CotangentComplex.tensorModule φ F)⟦(1 : ℤ)⟧)

#check SheafOfModules.RingedSite.CotangentComplex.atiyahTriangle_mor₃
#check SheafOfModules.RingedSite.CotangentComplex.tensorModule
