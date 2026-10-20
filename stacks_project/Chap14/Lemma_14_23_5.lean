/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.LowerFace
public import ReasLib.AlgebraicTopology.SimplicialObject.EilenbergMacLane.NormalizedMoore
import StacksCheckRecall

/-!
# Lemma 14.23.5 compatibility facade

@stack 0199

The degreewise normalized Moore computation for an Eilenberg--MacLane object is owned by ReasLib.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Simplicial

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (B : A) (k i : ℕ)

/- Lemma 14.23.5 (1): degree `k` of the source-signed `N(K(B, k))` is canonically isomorphic to `B`. -/
@[stacks 0199]
#check (SimplicialObject.eilenbergMacLane.normalizedMoore.lowerFace.objIso B k :
  ((AlgebraicTopology.normalizedMooreComplex.lowerFace (A := A)).obj
      (SimplicialObject.eilenbergMacLane B k)).X k ≅ B)
#check SimplicialObject.eilenbergMacLane.normalizedMoore.lowerFace.objIso.hom_naturality
#check SimplicialObject.eilenbergMacLane.normalizedMoore.lowerFace.objIso.inv_naturality
#check SimplicialObject.eilenbergMacLane.normalizedMoore.lowerFace.subobject_eq_top B k

/- The reusable statement is natural in the coefficient object before degreewise evaluation. -/
#check (SimplicialObject.eilenbergMacLane.normalizedMoore.lowerFace.evalIso (A := A) k)
#check (SimplicialObject.eilenbergMacLane.normalizedMoore.lowerFace.evalIso_app (A := A) k B)

/- Lemma 14.23.5 (2): degree `i ≠ k` of `N(K(B, k))` is zero. -/
@[stacks 0199]
#check (SimplicialObject.eilenbergMacLane.normalizedMoore.lowerFace.isZero B k i :
  i ≠ k → IsZero (((AlgebraicTopology.normalizedMooreComplex.lowerFace (A := A)).obj
    (SimplicialObject.eilenbergMacLane B k)).X i))
#check SimplicialObject.eilenbergMacLane.normalizedMoore.lowerFace.isZero_comp_eval (A := A) k i
#check SimplicialObject.eilenbergMacLane.normalizedMoore.lowerFace.subobject_eq_bot B k i

/- The raw lower-face transport and Mathlib's d₀-oriented normalization remain
convention-specific companions. -/
#check CategoryTheory.Abelian.DoldKan.N.lowerFace
#check CategoryTheory.Abelian.DoldKan.N.lowerFace.equivalence
#check CategoryTheory.SimplicialObject.normalizedMoore.lowerFace.subobject
#check CategoryTheory.SimplicialObject.normalizedMoore.lowerFace.lastFace
#check CategoryTheory.Abelian.DoldKan.N.lowerFace.obj_X
#check CategoryTheory.Abelian.DoldKan.N.lowerFace.obj_d
#check (SimplicialObject.eilenbergMacLane.normalizedMoore.objIso B k :
  ((AlgebraicTopology.normalizedMooreComplex A).obj
      (SimplicialObject.eilenbergMacLane B k)).X k ≅ B)
#check SimplicialObject.eilenbergMacLane.normalizedMoore.isZero B k i

end CategoryTheory
