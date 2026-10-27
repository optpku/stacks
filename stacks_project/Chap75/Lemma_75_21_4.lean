/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.TensorPushforward

/-!
# Tensor-pushforward base change for a relatively flat bounded-above complex

Derived pushforward of a quasi-coherent derived object tensored with a relatively flat
bounded-above complex commutes with arbitrary base change, using ordinary termwise
pullback of the complex on the right.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits

universe u

/- Lemma 75.21.4: tensor-pushforward base change for a relatively flat bounded-above
complex of quasi-coherent modules on an algebraic space. -/
@[stacks 0A1K] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardTensorBaseChange_isIso :
    ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g)
    (E : DerivedQCoh X) (G : CochainComplex (Modules X) ℤ)
    (hG_minus : CochainComplex.minus (Modules X) G)
    (hG_qcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hG_flat : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x),
    IsIso (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.tensorPushforwardBaseChange
      g' f' f g sq E G))
