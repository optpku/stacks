/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedPoints
import StacksCheckRecall

/-!
# Algebraic residue-field extensions yield closed points of decent spaces

On a decent algebraic space, a field-valued point over a closed point of the
base with algebraic residue-field extension is a closed point of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Scheme.Hom

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.14.4: Let `S` be a scheme and `X` a decent algebraic space over `S`.
Given a commutative diagram `Spec(k) ⟶ X` over `S`, if the image `s` of
`Spec(k) ⟶ S` is a closed point and `κ(s) ⊂ k` is algebraic, then the image
`x` of `Spec(k) ⟶ X` is a closed point of `|X|`. -/
@[stacks 07U5] #check
  (AlgebraicGeometry.AlgebraicSpace.mem_closedPoints_of_isAlgebraic_residueField :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (p : FieldValuedPoint X),
      closedPointImage p.structureHom ∈ closedPoints S →
      Algebra.IsAlgebraic (S.residueField (closedPointImage p.structureHom)) p.K →
      Points.mk p ∈ closedPoints (Points X))

end AlgebraicGeometry.AlgebraicSpace
