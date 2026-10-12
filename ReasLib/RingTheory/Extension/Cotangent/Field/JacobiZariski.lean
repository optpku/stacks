/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.JacobiZariski.FilteredColimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Jacobi-Zariski for towers of fields

The middle exactness and right surjectivity of the Jacobi-Zariski sequence are
canonical mathlib API. This leaf owns the additional injectivity of its left
edge for a tower of fields.

@stack 07E2
-/

@[expose] public section

open scoped TensorProduct

noncomputable section

universe u v w

namespace Algebra.H1Cotangent

/-- Lemma 15.34.2 (1), tag `07E2`: for a tower of
fields `K → L → M`, the left edge
`M ⊗[L] H1Cotangent K L ⟶ H1Cotangent K M` of the Jacobi-Zariski
sequence is injective. -/
@[stacks 07E2 "(1)"]
theorem liftBaseChange_map_injective
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M] :
    Function.Injective (LinearMap.liftBaseChange M (map K K L M)) := sorry

end Algebra.H1Cotangent
