/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Atiyah.Triangle
import StacksCheckRecall

universe u

open CategoryTheory

/- Definition 92.17.1: Let A → B be a ring map. Let M be a B-module.
The map M ⟶ (L_{B/A} ⊗^L_B M)⟦1⟧ in 92.17.0.1 is called the Atiyah class of M.
This is Algebra.CotangentComplex.Atiyah.connectingMap, equivalently the third
arrow of Algebra.CotangentComplex.Atiyah.triangle. -/
@[stacks 09DE]
#check (Algebra.CotangentComplex.Atiyah.connectingMap :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat.{u} B),
    (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M ⟶
      (Algebra.CotangentComplex.Atiyah.tensorModule A B M)⟦(1 : ℤ)⟧)

#check (Algebra.CotangentComplex.Atiyah.triangle_mor₃ :
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat.{u} B),
    (Algebra.CotangentComplex.Atiyah.triangle A B M).mor₃ =
      Algebra.CotangentComplex.Atiyah.connectingMap A B M)
#check Algebra.CotangentComplex.Atiyah.tensorModule
