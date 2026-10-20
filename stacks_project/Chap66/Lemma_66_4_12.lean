/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Monomorphism
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

/- Lemma 66.4.12: let `S` be a scheme. Let `X` be an algebraic space over `S`.
The assignment sending a monomorphism `Spec(k) ⟶ X`, with `k` a field, to its
class in `|X|` is injective. -/
@[stacks 03E1] #check
  (AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.unique_iso_of_mono :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {p q : FieldValuedPoint X}
      [Mono p.hom] [Mono q.hom],
      Points.mk p = Points.mk q →
        Nonempty (p ≅ q) ∧ Subsingleton (p ≅ q))
