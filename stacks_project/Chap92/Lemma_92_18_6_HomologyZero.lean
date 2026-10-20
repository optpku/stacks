/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.HomologyZero

/-!
# Degree-zero comparison for the sheaf cotangent complex

The canonical comparison and its isomorphism are available from the mathematical owner.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite
open scoped SheafOfModules.RingedSite.CotangentComplex

universe u

#check (SheafOfModules.RingedSite.CotangentComplex.homologyZeroIso :
    ∀ {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
      [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
      [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
      [HasWeakSheafify J CommRingCat.{u}]
      [HasWeakSheafify J AddCommGrpCat.{u}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B),
      L(φ).homology 0 ≅ Ω(φ))

#check (SheafOfModules.RingedSite.CotangentComplex.homologyZeroMap :
    ∀ {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
      [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
      [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
      [HasWeakSheafify J CommRingCat.{u}]
      [HasWeakSheafify J AddCommGrpCat.{u}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      {A B : Sheaf J CommRingCat.{u}} (φ : A ⟶ B),
      L(φ).homology 0 ⟶ Ω(φ))
