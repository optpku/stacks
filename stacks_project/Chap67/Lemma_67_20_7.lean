/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeSpectrum.Equivalence

@[expose] public section

open CategoryTheory

universe u

/- Lemma 67.20.7 (1): algebraic spaces affine over an algebraic space are
anti-equivalent to quasi-coherent algebras by pushforward of structure sheaves. -/
@[stacks 081V] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver.exists_pushforwardEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
      ∃ e : (AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver X)ᵒᵖ ≌
          AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder X,
        AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver.IsPushforwardEquivalence X e)

/- Lemma 67.20.7 (2): the anti-equivalence is compatible with arbitrary base
change of algebraic spaces over the same scheme. -/
@[stacks 081V] #check
  (AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver.exists_baseChangeCompatiblePushforwardEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
      ∃ eX : (AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver X)ᵒᵖ ≌
          AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder X,
        AlgebraicGeometry.AlgebraicSpace.AffineMorphismOver.IsBaseChangeCompatible X eX)

