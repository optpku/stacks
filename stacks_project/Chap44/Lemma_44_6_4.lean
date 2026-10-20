/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Rigidified.PushforwardLine.Representability
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RigidifiedPicard

/- Lemma 44.6.4: if `X` is a smooth projective geometrically irreducible curve of genus `g`
over `k` with `k`-rational point `σ`, then the pushforward-line subfunctor is represented by
an open subscheme of the degree-`g` Hilbert scheme of `X`. -/
@[stacks 0B9X] #check
  (AlgebraicGeometry.RigidifiedPicard.pushforwardLineSubfunctor_representableByOpenHilbertSubscheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
    [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
    (σ : Spec (CommRingCat.of k) ⟶ X.left) (hσ : σ ≫ X.hom = 𝟙 _)
    (g : ℕ) (h_genus : Curve.genus X = g),
    ∃ (U : (Hilbert.functor X g).reprX.left.Opens)
      (ξU : (pushforwardLineSubfunctor X σ hσ).toFunctor.obj
        (op (Over.mk (U.ι ≫ (Hilbert.functor X g).reprX.hom)))),
      (pushforwardLineSubfunctor X σ hσ).toFunctor.IsRepresentedBy ξU)

end AlgebraicGeometry.RigidifiedPicard
