/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Lemma_71_6_12_Pullback
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 71.6.10
Let `S` be a scheme. Let `f : X' ⟶ X` be a morphism of algebraic spaces over `S`.
Let `D ⊂ X` be an effective Cartier divisor. The pullback of `D` by `f` is defined
when the inverse-image closed subspace `D.inverseImage f ⊂ X'` is an effective
Cartier divisor. In that case the pullback is that inverse image, written `f^*D`
or `f⁻¹(D)`. -/
@[stacks 083Y] #check
  (ClosedSubspace.pullbackDefined :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
      ClosedSubspace X → (Y ⟶ X) → Prop)

#check
  (ClosedSubspace.pullbackDefined_iff :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
      (D : ClosedSubspace X) → (f : Y ⟶ X) →
        D.pullbackDefined f ↔
          IsEffectiveCartierDivisor (D.inverseImage f).ι)
