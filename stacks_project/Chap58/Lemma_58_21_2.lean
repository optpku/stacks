/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.Purity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

/- Lemma 58.21.2: for a flat morphism `f : X ⟶ Y` of locally Noetherian schemes,
if `f` is finite-type quasi-finite at `x`, `x` is not a generic point of an
irreducible component of `X`, and `f` is unramified at every codimension-one
specialization of `x`, then `f` is étale at `x`. -/
@[stacks 0BJH] #check
  (AlgebraicGeometry.Scheme.Hom.etaleAt_of_purity_branchLocus :
    ∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
      [AlgebraicGeometry.IsLocallyNoetherian X]
      [AlgebraicGeometry.IsLocallyNoetherian Y]
      [AlgebraicGeometry.Flat f],
      ∀ (x : X),
        AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt f x →
          x ∉ genericPoints X →
            (∀ x' : X, x' ⤳ x →
              ringKrullDim (X.presheaf.stalk x') = 1 →
                AlgebraicGeometry.Scheme.Hom.UnramifiedAt f x') →
              AlgebraicGeometry.Scheme.Hom.EtaleAt f x)
