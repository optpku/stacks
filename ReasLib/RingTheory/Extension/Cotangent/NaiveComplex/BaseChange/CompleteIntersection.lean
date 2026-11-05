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

/-- Lemma 15.86.5 (0FV1): in the canonical cocartesian square, if both vertical maps are local
complete intersections, the kernel of the comparison on degree-minus-one homology of the
base-changed naive cotangent complex of any presentation is finite projective over the pushout.
The source is the homology of the base-changed complex, so its differential is tensorized before
taking the kernel. -/
@[stacks 0FV1 "finite-projective kernel of H1 cotangent base change"]
theorem baseChangeComparison_ker_finiteProjective
    {ι σ : Type u}
    [RingHom.IsLocalCompleteIntersection (algebraMap A B)]
    [RingHom.IsLocalCompleteIntersection (algebraMap A' B')]
    (P : Algebra.Presentation A B ι σ) :
    Module.FiniteProjective B'
      ↥(LinearMap.ker
        (Algebra.Presentation.naiveCotangentBaseChangeH1Comparison (R' := A') P)) := sorry
/- Proof strategy: use the presentation-level comparison from 0FUZ. The two LCI hypotheses make
the naive cotangent complexes perfect of Tor amplitude `[-1, 0]`, as is the base-changed source.
The comparison's homotopy fibre has only degree-one homology, equal to this kernel; perfectness
and Tor amplitude imply that this homology module is finitely presented and flat, hence finite
projective. -/

end Algebra.H1Cotangent
