/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Algebra.TensorProduct
public import ReasLib.RingTheory.CohenMacaulay.Ring
public import ReasLib.RingTheory.EssentialFiniteness

/-!
# Cohen--Macaulay tensor products of field extensions

The symmetric finite-type hypothesis is the reusable owner.  One-sided
specializations are provided as thin bridges, but no global instance is
registered because the chosen base field and the two algebra structures are
part of the theorem's data.

@stack 045M
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace CohenMacaulayRing

variable {k : Type u} [Field k]
variable {K : Type v} [Field K] [Algebra k K]
variable {L : Type w} [Field L] [Algebra k L]

/-- Lemma 10.167.1 (Stacks tag `045M`): if either field extension over `k` is
essentially of finite type, their tensor product is Cohen--Macaulay. -/
@[stacks 045M]
theorem tensorProduct_of_essFiniteType
    (h : Algebra.EssFiniteType k K ∨ Algebra.EssFiniteType k L) :
    CohenMacaulayRing (K ⊗[k] L) := sorry

/-- Left-sided specialization of `tensorProduct_of_essFiniteType`. -/
theorem tensorProduct_of_essFiniteType_left
    [Algebra.EssFiniteType k K] :
    CohenMacaulayRing (K ⊗[k] L) := sorry

/-- Right-sided specialization of `tensorProduct_of_essFiniteType`. -/
theorem tensorProduct_of_essFiniteType_right
    [Algebra.EssFiniteType k L] :
    CohenMacaulayRing (K ⊗[k] L) := sorry

end CohenMacaulayRing
