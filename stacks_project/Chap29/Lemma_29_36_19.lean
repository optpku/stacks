/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Descent

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 29.36.19
The composite formulation below is equivalent to the source's commutative-triangle
formulation by rewriting `p` with `f ≫ q = p`.
-/
@[stacks 02K6] #check
  (AlgebraicGeometry.Etale.of_comp_surjective :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f],
      Etale f → Etale (f ≫ q) → LocallyOfFinitePresentation q → Etale q)
