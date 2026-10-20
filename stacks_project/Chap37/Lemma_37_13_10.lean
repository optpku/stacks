/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.Transitivity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 37.13.10: for scheme morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, the canonical
six-term naive-cotangent sequence is exact, and its final comparison map is epic, encoding the
terminal map to zero. -/
@[stacks 0E44] #check (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.sixTerm_exact :
  ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    let t := RingedSpace.NaiveCotangent.transitivity f.toShHom g.toShHom
    t.sixTerm.Exact ∧ Epi (HomologicalComplex.homologyMap t.comparison 0))
