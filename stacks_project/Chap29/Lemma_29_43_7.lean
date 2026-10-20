/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Composition
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.43.7: a composition of H-projective morphisms is H-projective. -/
@[stacks 01WE] #check (AlgebraicGeometry.HProjective.comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z},
    AlgebraicGeometry.HProjective f → AlgebraicGeometry.HProjective g →
      AlgebraicGeometry.HProjective (f ≫ g))
