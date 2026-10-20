/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.EulerCharacteristic.MultiTwist
import StacksCheckRecall

/-!
# Lemma 72.18.1

The Euler characteristic of integral multi-twists of a coherent module on an
algebraic space proper over a field is a numerical polynomial whose total
degree is at most the dimension of the scheme-theoretic support.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.Modules.TensorPower
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Lemma 72.18.1: let `k` be a field, let `X` be a proper algebraic space over `k`,
let `F` be a coherent `𝒪_X`-module, and let `L 1, …, L r` be invertible
`𝒪_X`-modules. The map `n ↦ χ(X, F ⊗ L 1^{⊗ n 1} ⊗ ⋯ ⊗ L r^{⊗ n r})` is a
numerical polynomial in `n 1, …, n r` of total degree at most the dimension of
the scheme-theoretic support of `F`. -/
@[stacks 0DN4] #check
  (AlgebraicGeometry.AlgebraicSpace.eulerCharacteristic_multiTwist_isMvNumericalPolynomialOfTotalDegreeLE :
    ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Proper (SchemeRealization.toBase X)] [IsLocallyNoetherian X]
    [Abelian X.Modules]
    [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))).Modules]
    [HasInjectiveResolutions X.Modules]
    (F : X.Modules) [F.IsCoherent] {r : ℕ} (L : Fin r → X.Modules)
    [∀ j : Fin r, isInvertibleObject (L j)],
    IsMvNumericalPolynomialOfTotalDegreeLE
      (fun n ↦ eulerCharacteristic (𝟙 (Spec (CommRingCat.of k))) (SchemeRealization.toBase X)
        (multiTwist F L n))
      (dimension (schemeTheoreticSupport F).X))

end AlgebraicGeometry.AlgebraicSpace
