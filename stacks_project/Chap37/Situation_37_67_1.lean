/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan

open CategoryTheory

universe u

/- Situation 37.67.1: let `S` be a scheme and let `i : Z ⟶ X` and `j : Z ⟶ Y`
be morphisms of schemes over `S`. The morphism `i` is a closed immersion, `j` is
integral, and for every `y : Y` there is an affine open `U ⊆ X` such that the fibre
of `j` over `y` is contained in the inverse image of `U` under `i`. -/
@[stacks 0ECI] #check (@AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {Z X Y : CategoryTheory.Over S} →
      (Z ⟶ X) → (Z ⟶ Y) → Prop)

#check AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan.iff
