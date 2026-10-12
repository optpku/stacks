/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.EulerCharacteristic
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Definition 72.17.1: for a field `k`, an algebraic space `X` proper over `k`, and a
coherent `𝒪_X`-module `F`, the Euler characteristic `χ(X, F)` is the integer
given by the signed finite sum of the dimensions of its cohomology groups. -/
@[stacks 0DN1] #check
  (AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules.eulerCharacteristic :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (CommRingCat.of k)))
      [AlgebraicSpace.Proper (AlgebraicSpace.SchemeRealization.toBase X)]
      (F : AlgebraicSpace.SmallEtale.Modules X)
      [AlgebraicSpace.SmallEtale.Modules.IsCoherent F], ℤ)

#check
  (AlgebraicGeometry.AlgebraicSpace.SmallEtale.Modules.eulerCharacteristic_def :
    ∀ {k : Type u} [Field k] (X : AlgebraicSpace (Spec (CommRingCat.of k)))
      [AlgebraicSpace.Proper (AlgebraicSpace.SchemeRealization.toBase X)]
      (F : AlgebraicSpace.SmallEtale.Modules X)
      [AlgebraicSpace.SmallEtale.Modules.IsCoherent F],
      AlgebraicSpace.SmallEtale.Modules.eulerCharacteristic X F =
        ∑ᶠ degree : ℕ,
          ((degree : ℤ).negOnePow : ℤ) *
            (Module.finrank k (AlgebraicSpace.SmallEtale.Modules.cohomology F degree) : ℤ))
