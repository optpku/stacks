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

/- 92.19.0.2: on a site, for a homomorphism of ring sheaves φ : A ⟶ B and a B-module sheaf F,
the degreewise first principal-parts extensions of F along the standard resolution P_• ⟶ B
assemble to a short exact sequence of simplicial P_•-modules. Applying
Lπ_! : D(P_•) ⟶ D(B) yields the distinguished triangle
L(φ) ⊗^L F ⟶ Lπ_!(P¹_{P_•/A}(F)) ⟶ F ⟶ (L(φ) ⊗^L F)⟦1⟧ in D(B). -/
@[stacks 09DH]
#check (SheafOfModules.RingedSite.CotangentComplex.atiyahTriangle_distinguished φ F :
  SheafOfModules.RingedSite.CotangentComplex.atiyahTriangle φ F ∈
    distTriang
      (RingedSite.Hom.ModuleDerived (RingedSite.ofCommRingSheaf J B)))
