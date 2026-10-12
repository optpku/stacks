/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Diagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Smooth

/- Lemma 37.62.18: for a finite-type morphism of locally Noetherian schemes, smoothness is
equivalent to flatness together with the diagonal being a regular immersion, a local
complete-intersection morphism, or a perfect morphism. -/
@[stacks 0FDP] #check (AlgebraicGeometry.Smooth.diagonal_tfae :
  {X Y : Scheme.{u}} → (f : X ⟶ Y) → [Scheme.Hom.FiniteType f] →
    [IsLocallyNoetherian X] → [IsLocallyNoetherian Y] →
    List.TFAE [Smooth f,
      Flat f ∧ IsRegularImmersion (pullback.diagonal f),
      Flat f ∧ LocallyOfType RingHom.IsLocalCompleteIntersection (pullback.diagonal f),
      Flat f ∧ LocallyOfType RingHom.IsPerfectRingMap (pullback.diagonal f)])

end AlgebraicGeometry.Smooth
