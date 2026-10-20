/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import stacks_project.Chap36.«36_6_4_1»
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory.Limits

universe u

/- Remark 36.6.4: `ModuleCech.ofSections f ℱ` is the bounded extended alternating Čech
complex on the principal opens `X.basicOpen (f i)`, with `ℱ` in degree zero and signed
restriction differentials. -/
@[stacks 0G7I] #check
  (ModuleCech.ofSections :
    {X : Scheme.{u}} → {c : ℕ} → (Fin c → Γ(X, ⊤)) → X.Modules →
      CochainComplex X.Modules ℕ)

/- The original module sheaf occupies degree zero. -/
@[stacks 0G7I] #check ModuleCech.ofSections_X_zero

/- Positive degrees are the finite biproducts indexed by strictly increasing tuples. -/
@[stacks 0G7I] #check ModuleCech.ofSections_X_succ

/- Every degree strictly above the number of principal opens is zero. -/
#check
  (ModuleCech.ofSections_isZero_of_lt :
    {X : Scheme.{u}} → {c n : ℕ} → (f : Fin c → Γ(X, ⊤)) → (ℱ : X.Modules) →
      c < n → IsZero ((ModuleCech.ofSections f ℱ).X n))

/- Deleting an index induces the canonical restriction map between the corresponding summands. -/
@[stacks 0G7I] #check AlgebraicGeometry.Scheme.ModuleCech.Ordered.restriction

/- Each differential component is the alternating sum of the canonical restriction maps. -/
@[stacks 0G7I] #check AlgebraicGeometry.Scheme.ModuleCech.Ordered.differential_π
