/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Integral.Product
import StacksCheckRecall

universe u

/- Lemma 32.3.3: if each morphism `T i ⟶ S` is integral, then the product
of the family in `CategoryTheory.Over S` is integral over `S`. -/
@[stacks 0CNK] #check
  (AlgebraicGeometry.Scheme.Over.instIsIntegralHomPiObj :
    ∀ {I : Type u} (S : AlgebraicGeometry.Scheme.{u})
      (T : I → CategoryTheory.Over S)
      [∀ i, AlgebraicGeometry.IsIntegralHom (T i).hom],
      AlgebraicGeometry.IsIntegralHom (CategoryTheory.Limits.piObj T).hom)
