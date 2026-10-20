/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
import StacksCheckRecall

universe u

open CategoryTheory

/- Definition 31.34.1: A morphism `X' ⟶ X` is a `U`-admissible blowup if it is the
blowup in a finitely presented closed subscheme disjoint from `U`. -/
@[stacks 080K] #check (AlgebraicGeometry.IsAdmissibleBlowup :
  {X X' : AlgebraicGeometry.Scheme.{u}} → X.Opens → (X' ⟶ X) → Prop)

#check (AlgebraicGeometry.isAdmissibleBlowup_iff :
  ∀ {X X' : AlgebraicGeometry.Scheme.{u}} (U : X.Opens) (f : X' ⟶ X),
    AlgebraicGeometry.IsAdmissibleBlowup U f ↔
      ∃ I : X.IdealSheafData,
        AlgebraicGeometry.IsBlowup f I ∧
          AlgebraicGeometry.LocallyOfFinitePresentation I.subschemeι ∧
            Disjoint (I.support : Set X) U)
