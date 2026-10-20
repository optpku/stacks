/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.ChernCharacter
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/- Lemma 50.21.3: for qcqs schemes over `ℚ`, there is a unique pullback-natural Chern
character ring homomorphism to completed even relative de Rham cohomology, sending a line
bundle class to the exponential of its first de Rham Chern class. -/
@[stacks 0FWB] #check
  (AlgebraicGeometry.Scheme.DeRham.Rational.existsUniqueChernCharacter :
    ∃! ch : ∀ X : Rational.QcqsScheme.{u},
      VectorBundleK0 X.obj.left →+* Rational.CompletedEven X.obj,
      Rational.IsNatural ch ∧ Rational.LineBundleNormalized ch)

end AlgebraicGeometry.Scheme.DeRham
