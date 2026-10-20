/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange.Homology
public import ReasLib.RingTheory.Finiteness.Projective.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naive cotangent base change for local complete intersections

@stack 0FV1
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

namespace Algebra.H1Cotangent

variable {A A' B : Type u}
variable [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B]

local notation "B'" => A' ⊗[A] B

-- Local instance justification (instance diamond): keep both canonical tensor-factor algebra
-- structures local to this source-facing pushout statement.
attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

-- The kernel is a canonical `B'`-submodule; pin its inherited module structure for the
-- `Module.FiniteProjective` statement.
/-- Local instance justification (defeq pin): use the comparison kernel's inherited module
structure over the tensor-product base. -/
local instance :
    Module B'
      ↥(LinearMap.ker
        (baseChangeComparison (R := A) (R' := A') (S := B))) :=
  Submodule.module
    (LinearMap.ker (baseChangeComparison (R := A) (R' := A') (S := B)))

/-- Lemma 15.86.5 (0FV1): in the canonical cocartesian square, if both vertical maps are local
complete intersections, the kernel of the degree-minus-one naive-cotangent base-change
comparison is a finite projective module over the pushout. -/
@[stacks 0FV1 "finite-projective kernel of H1 cotangent base change"]
theorem baseChangeComparison_ker_finiteProjective
    [RingHom.IsLocalCompleteIntersection (algebraMap A B)]
    [RingHom.IsLocalCompleteIntersection (algebraMap A' B')] :
    Module.FiniteProjective B'
      ↥(LinearMap.ker
        (baseChangeComparison (R := A) (R' := A') (S := B))) := sorry
/- Proof strategy: compare the two Jacobi-Zariski triangles for the pushout square.  The two LCI
hypotheses make the relevant naive cotangent objects perfect of Tor amplitude `[-1, 0]`; use the
surjective `H1` comparison and the degree-zero base-change isomorphism to identify its kernel with
a finite projective homology summand. -/

end Algebra.H1Cotangent
