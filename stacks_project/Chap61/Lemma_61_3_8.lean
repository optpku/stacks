/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Spec.Over
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite AlgebraicGeometry

universe u

/- Lemma 61.3.8: for a ring `A` with `X = Spec A`, the functor sending an
`A`-algebra whose structure map identifies local rings to `Spec` of that algebra,
viewed in topological spaces over `X`, is fully faithful. -/
@[stacks 096L] #check
  (AlgebraicGeometry.Spec.toOverTopOnLocalRings_map_bijective :
    ∀ {A : CommRingCat.{u}}
      {B C : (RingHom.IsIsoOnLocalRings.Under A)ᵒᵖ},
      Function.Bijective
        ((AlgebraicGeometry.Spec.toOverTopOnLocalRings A).map :
          (B ⟶ C) →
            ((AlgebraicGeometry.Spec.toOverTopOnLocalRings A).obj B ⟶
              (AlgebraicGeometry.Spec.toOverTopOnLocalRings A).obj C)))
