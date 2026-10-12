/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Torsion-freeness under flat scalar extension

This file records torsion-freeness under flat scalar extension between domains. The tensor product
is kept in the canonical orientation `R' ⊗[R] M`.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Module.IsTorsionFree

variable {R : Type u} {R' : Type v} {M : Type w}
variable [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup M] [Module R M]

/-- Flat scalar extension of a torsion-free module over a domain is torsion-free over the
target domain. -/
@[stacks 0AXM "torsion-free flat tensor base change"]
instance baseChange_of_flat [IsDomain R] [IsDomain R'] [Flat R R']
    [IsTorsionFree R M] :
    IsTorsionFree R' (R' ⊗[R] M) := sorry
-- Proof strategy: embed `M` into its fraction-field tensor, apply flatness to the injection, and
-- use the canonical fraction-field localization and tensor reassociation maps to descend
-- torsion-freeness to `R' ⊗[R] M`.

end Module.IsTorsionFree
