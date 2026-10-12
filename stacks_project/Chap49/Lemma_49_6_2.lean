/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Kaehler.NoetherDifferent.BaseChange

open scoped TensorProduct

universe u v w

/- Lemma 49.6.2 (1): under a flat base change `A → A'`, the annihilator of the
kernel of multiplication for `A' ⊗[A] B` is the extension of the corresponding
annihilator for `B`. -/
@[stacks 0BVM] #check
  (KaehlerDifferential.annihilator_baseChange :
    ∀ (A : Type u) (A' : Type v) (B : Type w)
        [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B]
        [Algebra.FiniteType A B] [Module.Flat A A'],
      (KaehlerDifferential.ideal A' (A' ⊗[A] B)).annihilator =
        Ideal.map (Algebra.TensorProduct.diagonalBaseChange A A' B)
          (KaehlerDifferential.ideal A B).annihilator)

/- Lemma 49.6.2 (2): under the same flat base change, the Noether different of
`A' ⊗[A] B` is the extension of the Noether different of `B` over `A`. -/
@[stacks 0BVM] #check
  (KaehlerDifferential.noetherDifferent_baseChange :
    ∀ (A : Type u) (A' : Type v) (B : Type w)
        [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B]
        [Algebra.FiniteType A B] [Module.Flat A A'],
      KaehlerDifferential.noetherDifferent A' (A' ⊗[A] B) =
        Ideal.map Algebra.TensorProduct.includeRight
          (KaehlerDifferential.noetherDifferent A B))
