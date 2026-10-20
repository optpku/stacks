/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Compactification

public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 53.2.5: a morphism from a curve to a proper variety over a field factors through an
open immersion into a projective curve. -/
@[stacks 0BY0] #check (AlgebraicGeometry.Curve.exists_factor_through_projective_curve :
    ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} [Curve X] [Variety Y] [IsProper Y.hom]
    (f : X ⟶ Y),
    ∃ (Xbar : SchemeOverField k) (j : X ⟶ Xbar) (g : Xbar ⟶ Y)
      (_ : IsOpenImmersion j.left) (_ : Curve Xbar) (_ : Projective Xbar.hom),
      j ≫ g = f)
