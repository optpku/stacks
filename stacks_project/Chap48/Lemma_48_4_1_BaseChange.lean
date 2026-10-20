/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.BaseChange.RightAdjoint
public import stacks_project.Chap36.Lemma_36_4_1

public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- This typed compatibility bridge preserves the historical import surface for the
right-adjoint derived base-change transformation. -/
#check
  (@AlgebraicGeometry.Scheme.DerivedQCoh.BaseChange.rightMate :
    ∀ {X' X Y' Y : Scheme.{u}}
      (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
      [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
      [QuasiCompact g] [QuasiSeparated g] [QuasiCompact g'] [QuasiSeparated g']
      (sq : CommSq g' f' f g)
      (a : Scheme.DerivedQCoh Y ⥤ Scheme.DerivedQCoh X)
      (a' : Scheme.DerivedQCoh Y' ⥤ Scheme.DerivedQCoh X')
      (fAdj : Scheme.DerivedQCoh.pushforwardCohomologyIn f ⊣ a)
      (f'Adj : Scheme.DerivedQCoh.pushforwardCohomologyIn f' ⊣ a'),
      a' ⋙ Scheme.DerivedQCoh.pushforwardCohomologyIn g' ⟶
        Scheme.DerivedQCoh.pushforwardCohomologyIn g ⋙ a)
