/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.41.9 (1): if `f : X ⟶ Y` is surjective and `f ≫ g : X ⟶ S` is
universally closed, then `g : Y ⟶ S` is universally closed. -/
@[stacks 03GN] #check
  (AlgebraicGeometry.UniversallyClosed.of_comp_surjective :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [AlgebraicGeometry.UniversallyClosed (f ≫ g)] [AlgebraicGeometry.Surjective f],
      AlgebraicGeometry.UniversallyClosed g)

/- Lemma 29.41.9 (2): if `f : X ⟶ Y` is surjective and `f ≫ g : X ⟶ S` is
universally closed, then a separated, locally finite type `g : Y ⟶ S` is proper. -/
@[stacks 03GN] #check
  (AlgebraicGeometry.IsProper.of_comp_surjective :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
      [AlgebraicGeometry.Surjective f] (_ : AlgebraicGeometry.UniversallyClosed (f ≫ g))
      [AlgebraicGeometry.IsSeparated g] [AlgebraicGeometry.LocallyOfFiniteType g],
      AlgebraicGeometry.IsProper g)
