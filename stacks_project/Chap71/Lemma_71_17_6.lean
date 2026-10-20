/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.EffectiveCartier
import StacksCheckRecall

/-!
# Lemma 71.17.6

The blowup of an algebraic space along an effective Cartier divisor is the
identity morphism of that algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 71.17.6: let `S` be a scheme. Let `X` be an algebraic space over `S`.
Let `Z ⊂ X` be an effective Cartier divisor. The blowup of `X` in `Z` is the
identity morphism of `X`. -/
@[stacks 085V] #check (AlgebraicGeometry.AlgebraicSpace.Blowup.isIso_hom :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    [IsEffectiveCartierDivisor Z.ι] (π : Blowup.along Z), IsIso π.hom)

#check (AlgebraicGeometry.AlgebraicSpace.Blowup.isoOver_id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    [IsEffectiveCartierDivisor Z.ι] (π : Blowup.along Z),
    Nonempty (Over.mk π.hom ≅ Over.mk (𝟙 X)))
