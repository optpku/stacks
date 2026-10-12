/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissageAtAmbientPoint.EtaleRefinement
import StacksCheckRecall

universe u

open AlgebraicGeometry

/- Lemma 38.4.8: an ambient-point one-step dévissage can be refined along a pointed
elementary étale refinement square. -/
@[stacks 05HE] #check
  (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.nonemptyEtaleRefinement :
    {S : Scheme.{u}} → {X : CategoryTheory.Over S} → {F : X.left.Modules} →
      [LocallyOfFiniteType X.hom] → [F.IsQuasicoherent] → [F.IsFiniteType] →
        {x : X.left} →
          (D : AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint X F x) →
          (square : AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary.RefinementSquare
            D.toOneStepDevissage.Y.hom D.y) →
          Nonempty
            (AlgebraicGeometry.Scheme.Modules.OneStepDevissageAtAmbientPoint.EtaleRefinement
              D square))
