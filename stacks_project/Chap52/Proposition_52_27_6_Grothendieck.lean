/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.CompleteIntersection
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/- Proposition 52.27.6 (Grothendieck): for a Noetherian local complete-intersection ring `A`
of Krull dimension at least four, the Picard group of its punctured spectrum is trivial. -/
@[stacks 0F2I] #check
  (AlgebraicGeometry.PuncturedSpectrum.subsingletonPicardGroup_of_completeIntersection :
  ∀ {A : Type u} [CommRing A] [IsCompleteIntersectionLocalRing A]
    [Fact ((4 : WithBot ℕ∞) ≤ ringKrullDim A)],
    Subsingleton (AlgebraicGeometry.Scheme.PicardGroup
      (AlgebraicGeometry.PuncturedSpectrum.scheme A)))

end AlgebraicGeometry.PuncturedSpectrum
