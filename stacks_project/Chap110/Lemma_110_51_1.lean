/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.Specialization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 110.51.1: there exists an étale morphism of algebraic spaces `f : X ⟶ Y`
and a nontrivial specialization of points `x ⤳ x'` in `|X|` with `f(x) = f(x')`
in `|Y|`. -/
@[stacks 06UK] #check
  (AlgebraicGeometry.AlgebraicSpace.exists_etale_nontrivial_specialization_in_fibre :
    ∃ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y) (x x' : Points X),
      Etale f ∧ Specializes x x' ∧ x ≠ x' ∧ Points.map f x = Points.map f x')

end AlgebraicGeometry.AlgebraicSpace
