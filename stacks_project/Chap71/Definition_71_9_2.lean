/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_9_2_RelativeEffectiveCartier
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Definition 71.9.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. A relative effective Cartier divisor on `X/Y` is an
effective Cartier divisor `D ⊂ X` such that `D ⟶ Y` is a flat morphism of
algebraic spaces. -/
@[stacks 0EPP] #check
  (IsRelativeEffectiveCartierDivisor :
    {S : Scheme.{u}} → {D X Y : AlgebraicSpace S} → (X ⟶ Y) → (D ⟶ X) → Prop)

#check
  (isRelativeEffectiveCartierDivisor_iff :
    ∀ {S : Scheme.{u}} {D X Y : AlgebraicSpace S} (f : X ⟶ Y) (i : D ⟶ X),
      IsRelativeEffectiveCartierDivisor f i ↔
        IsEffectiveCartierDivisor i ∧ Flat (i ≫ f))
