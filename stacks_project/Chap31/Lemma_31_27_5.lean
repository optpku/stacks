/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory.MonoidalCategory

universe u

/- Lemma 31.27.5: on a locally Noetherian integral scheme, the tensor product of two nonzero
meromorphic sections of invertible modules is nonzero, its Weil divisor is the sum of their Weil
divisors, and the canonical Weil divisor class is additive under tensor product. -/
@[stacks 02SL] #check
  (AlgebraicGeometry.Scheme.nonzeroMeromorphicSectionWeilDivisor_tensor :
    ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
      {L N : X.Modules} [Scheme.Modules.Invertible L] [Scheme.Modules.Invertible N]
      (s : X.toLocallyRingedSpace.meromorphicSections L)
      (t : X.toLocallyRingedSpace.meromorphicSections N)
      (hs : s ≠ 0) (ht : t ≠ 0),
      (@Scheme.nonzeroMeromorphicSectionWeilDivisor X _ _ (L ⊗ N)
          (isInvertibleObject.tensor L N)
          (X.toLocallyRingedSpace.meromorphicSectionTensor s t)
          (AlgebraicGeometry.meromorphicSectionTensor_ne_zero s t hs ht)) =
        Scheme.nonzeroMeromorphicSectionWeilDivisor X L s hs +
          Scheme.nonzeroMeromorphicSectionWeilDivisor X N t ht)

#check
  (AlgebraicGeometry.meromorphicSectionTensor_ne_zero :
    ∀ {X : Scheme.{u}} [IsIntegral X]
      {L N : X.Modules} [Scheme.Modules.Invertible L] [Scheme.Modules.Invertible N]
      (s : X.toLocallyRingedSpace.meromorphicSections L)
      (t : X.toLocallyRingedSpace.meromorphicSections N),
      s ≠ 0 → t ≠ 0 → X.toLocallyRingedSpace.meromorphicSectionTensor s t ≠ 0)

#check
  (AlgebraicGeometry.Scheme.invertibleModuleWeilDivisorClass_tensor :
    ∀ (X : Scheme.{u}) [IsLocallyNoetherian X] [IsIntegral X]
      (L N : X.Modules) [Scheme.Modules.Invertible L] [Scheme.Modules.Invertible N],
      Scheme.invertibleModuleWeilDivisorClass X (L ⊗ N) =
        Scheme.invertibleModuleWeilDivisorClass X L +
          Scheme.invertibleModuleWeilDivisorClass X N)
