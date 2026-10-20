/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.StalkQuotient
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

/- Lemma [Stacks 0HA1] (1): for a morphism of schemes `f : X ⟶ S` and a point
`x : X`, viewing `x` as the distinguished point `f.asFiber x` of the
scheme-theoretic fibre `X_{f(x)}`, the local ring of the fibre is isomorphic
to the quotient of the source stalk by the extended maximal ideal of the
target stalk. -/
@[stacks 0HA1]
#check (AlgebraicGeometry.Scheme.Hom.fiberStalkAtEquivQuotient :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X),
    (f.fiber (f x)).presheaf.stalk (f.asFiber x) ≃+*
      (X.presheaf.stalk x ⧸
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).map (f.stalkMap x).hom))

/- Lemma [Stacks 0HA1] (2): the quotient of the source stalk by the extended
maximal ideal of the target stalk is isomorphic to the residue-field tensor
product `𝒪_{X, x} ⊗_{𝒪_{S, f(x)}} κ(f(x))`. -/
@[stacks 0HA1]
#check (AlgebraicGeometry.Scheme.Hom.sourceStalkQuotientEquivTensor :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X),
    (X.presheaf.stalk x ⧸
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).map (f.stalkMap x).hom) ≃+*
      X.presheaf.stalk x ⊗[S.presheaf.stalk (f x)] S.residueField (f x))
