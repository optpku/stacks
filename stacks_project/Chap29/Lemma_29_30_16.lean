/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Descent
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.30.16: in a commutative triangle `X -f-> Y -q-> S` and `X -p-> S`,
if `f` is surjective and syntomic, `p` is syntomic, and `q` is locally of finite
presentation, then `q` is syntomic.  Using `p = f ≫ q`, this is the following composite
formulation. -/
@[stacks 02K3] #check
  (AlgebraicGeometry.Syntomic.of_comp_surjective :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (q : Y ⟶ S)
      [AlgebraicGeometry.Surjective f]
      (_ : AlgebraicGeometry.Syntomic f) (_ : AlgebraicGeometry.Syntomic (f ≫ q))
      (_ : AlgebraicGeometry.LocallyOfFinitePresentation q),
      AlgebraicGeometry.Syntomic q)
