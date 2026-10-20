/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Cotangent.DerivedBaseChange

open CategoryTheory

universe u

#check (RingedSite.Cotangent.Functoriality.InducesDerivedTensorQuasiIso :
  ∀ {A A' B B' : CommRingCat.{u}} {α : A ⟶ B} {ρ : A ⟶ A'}
    {β : A' ⟶ B'} {φ : B ⟶ B'}, CommSq ρ α β φ → Prop)
