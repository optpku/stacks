/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex
import StacksCheckRecall

@[expose] public section

open SheafOfModules.RingedSite.CotangentComplex

universe u

/- Definition 92.18.2: Let C be a site. Let A ⟶ B be a homomorphism of sheaves of
rings on C. The cotangent complex L_{B/A} is the complex of B-modules associated
to the simplicial B-module Ω_{P_•/A} ⊗_{P_•, ε} B, where ε : P_• ⟶ B is the
standard resolution of B over A. We usually view L_{B/A} as an object of D(B)
via DerivedCategory.Q. -/
@[stacks 08SS]
#check (SheafOfModules.RingedSite.CotangentComplex.obj :
  ∀ {C : Type u} [CategoryTheory.Category.{u} C]
    {J : CategoryTheory.GrothendieckTopology C}
    [J.HasSheafCompose (CategoryTheory.forget₂ CommRingCat RingCat.{u})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
    [CategoryTheory.HasWeakSheafify J CommRingCat.{u}]
    [CategoryTheory.HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [CategoryTheory.Limits.HasColimitsOfShape
      (CategoryTheory.Discrete CategoryTheory.Limits.WalkingPair) CommRingCat.{u}]
    (A : CategoryTheory.Sheaf J CommRingCat.{u})
    (B : CategoryTheory.Under A),
    CochainComplex
      (SheafOfModules (SheafOfModules.RingedSite.ringSheaf J B.right)) ℤ)
