/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme.Classifying.FiniteType
import StacksCheckRecall

/-!
# Finite type of an affine group scheme from a smooth atlas of its classifying stack
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

universe u

/- Lemma 110.53.1: if `k` is a field and `G` is an affine group scheme over `k`,
and the classifying stack of fppf `G`-torsors admits a smooth covering by a
scheme, then `G` is of finite type over `k`. -/
@[stacks 04AH] #check
  (AlgebraicGeometry.GroupScheme.finiteType_of_classifyingStack_smoothCover :
    ∀ {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      [IsAffine G.X.left],
      (∃ (U : Over (Spec (CommRingCat.of k)))
        (p : Classifying.slice U ⟶ classifyingStack G),
        Classifying.Smooth p ∧ Classifying.Surjective p) →
      Scheme.Hom.FiniteType G.X.hom)
