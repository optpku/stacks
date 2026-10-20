/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.Characterization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.35.1: Characterizations of finite morphisms of algebraic spaces. -/
@[stacks 0A4X]
#check (AlgebraicGeometry.AlgebraicSpace.IsFinite.proper_discreteFieldFibers_tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    List.TFAE
      [ IsFinite f
      , Proper f ∧ LocallyQuasiFinite f
      , Proper f ∧ discreteFieldFibers f
      , UniversallyClosed f ∧ Separated f ∧ LocallyOfFiniteType f ∧
          discreteFieldFibers f ])
