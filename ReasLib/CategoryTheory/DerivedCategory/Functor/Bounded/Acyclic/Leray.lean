/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Basic

@[expose] public section

/-!
# Leray Acyclicity for Bounded Derived Functors

Termwise acyclicity of a bounded-below complex computes its pointwise right-derived value whenever
that value exists.  The bounded-above left-derived statement is exposed as the formal dual.  Both
statements use the canonical `RightDerived.ComputesAt` and `LeftDerived.ComputesAt` owners rather
than a comparison map tied to a chosen derived-category model.
-/

open CategoryTheory

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace RightAcyclic.Bounded.Termwise

/-- Stacks 015E (Leray acyclicity): a bounded-below complex of right-acyclic objects computes
its pointwise right-derived value.  Only existence at the given complex is required. -/
@[stacks 015E]
theorem computesAt
    {F : A ⥤ B} [F.Additive] {K : HomotopyCategory.Plus A}
    [F.toBoundedBelowDerived.HasPointwiseRightDerivedFunctorAt
      (HomotopyCategory.Plus.quasiIso A) K]
    (hK : RightAcyclic.Bounded.Termwise F K) :
    RightDerived.ComputesAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K := sorry

end RightAcyclic.Bounded.Termwise

namespace LeftAcyclic.Bounded.Termwise

/-- The formal dual of Leray acyclicity: a bounded-above complex of left-acyclic objects computes
its pointwise left-derived value whenever that value exists. -/
@[stacks 015E "formal dual"]
theorem computesAt
    {F : A ⥤ B} [F.Additive] {K : HomotopyCategory.Minus A}
    [F.toBoundedAboveDerived.HasPointwiseLeftDerivedFunctorAt
      (HomotopyCategory.Minus.quasiIso A) K]
    (hK : LeftAcyclic.Bounded.Termwise F K) :
    LeftDerived.ComputesAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K := sorry

end LeftAcyclic.Bounded.Termwise

end CategoryTheory.Functor
