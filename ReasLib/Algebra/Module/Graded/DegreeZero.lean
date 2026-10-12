/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.GradedMulAction
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Degree-zero modules on graded pieces

For an internally graded ring `𝒜` and a graded module family `ℳ`, a degree-zero
element preserves every homogeneous piece.  This leaf packages the induced module
structure on each piece.  Both families may use any additive-subgroup carrier, so
the construction applies without changing the chosen representation of homogeneous pieces.
-/

@[expose] public section

universe u v w x y z

namespace GradedModule

variable {ι : Type x} {κ : Type y} [DecidableEq ι] [AddMonoid ι] [AddAction ι κ]
variable {S : Type u} [Ring S] {M : Type v} [AddCommGroup M] [Module S M]
variable {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]
variable {τ : Type z} [SetLike τ M] [AddSubgroupClass τ M]

/-
API design: this is an instance rather than a chapter-local `letI`.  The only
non-inferable inputs are the graded algebra family, the graded piece family, and
the homogeneous-action proof; all ring/module laws are inherited from `S` and `M`.
The priority is deliberately below ordinary bundled module instances so that a
user's explicit module owner wins without an instance diamond.
-/

/-- The degree-zero part of an internally graded algebra acts on every graded module piece. -/
@[reducible, instance 100, stacks 052N "degree-zero graded piece module"]
def zeroPieceModule (𝒜 : ι → σ) [GradedRing 𝒜]
    (ℳ : κ → τ) [SetLike.GradedSMul 𝒜 ℳ] (j : κ) :
    Module (𝒜 0) (ℳ j) where
  smul a x := ⟨(a : S) • (x : M), by
    have h := SetLike.GradedSMul.smul_mem a.2 x.2
    simpa using h⟩
  one_smul x := by
    apply Subtype.ext
    change (1 : S) • (x : M) = (x : M)
    exact one_smul S (x : M)
  mul_smul a b x := by
    apply Subtype.ext
    change ((a : S) * (b : S)) • (x : M) = (a : S) • ((b : S) • (x : M))
    exact (smul_smul (a : S) (b : S) (x : M)).symm
  smul_add a x y := by
    apply Subtype.ext
    change (a : S) • ((x : M) + (y : M)) = (a : S) • (x : M) + (a : S) • (y : M)
    exact smul_add (a : S) (x : M) (y : M)
  smul_zero a := by
    apply Subtype.ext
    change (a : S) • (0 : M) = 0
    exact smul_zero (a : S)
  add_smul a b x := by
    apply Subtype.ext
    change ((a : S) + (b : S)) • (x : M) = (a : S) • (x : M) + (b : S) • (x : M)
    exact add_smul (a : S) (b : S) (x : M)
  zero_smul x := by
    apply Subtype.ext
    change (0 : S) • (x : M) = 0
    exact zero_smul S (x : M)

/-- Coercing the degree-zero action on a piece recovers the ambient scalar action. -/
@[simp, stacks 052N "degree-zero graded piece scalar formula"]
theorem coe_zeroPieceModule_smul (𝒜 : ι → σ) [GradedRing 𝒜]
    (ℳ : κ → τ) [SetLike.GradedSMul 𝒜 ℳ]
    (j : κ) (a : 𝒜 0) (x : ℳ j) :
    ((a • x : ℳ j) : M) = ((a : S) • (x : M) : M) := sorry

end GradedModule
