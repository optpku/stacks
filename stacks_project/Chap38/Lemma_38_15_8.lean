/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.Henselization

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 38.15.8: under Situation 38.15.1, existence of an impurity over a chosen
henselization, existence over an elementary étale neighbourhood, and existence over a
morphism quasi-finite at its special point are equivalent. -/
@[stacks 05J3] #check (AlgebraicGeometry.Scheme.Modules.Impurity.existence_tfae :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}}
      (F : X.Modules) (f : X ⟶ S) [AlgebraicGeometry.Scheme.Hom.FiniteType f]
      [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
      (Rh : Type u) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
      [IsHenselizationOf (S.presheaf.stalk s) Rh],
      List.TFAE [
        Nonempty
          (AlgebraicGeometry.Scheme.Modules.Impurity.Over F f s
            (AlgebraicGeometry.Scheme.Henselization.map S s Rh)
            (IsLocalRing.closedPoint Rh)),
        ∃ I : AlgebraicGeometry.Scheme.Modules.Impurity F f s, I.IsElementary,
        ∃ I : AlgebraicGeometry.Scheme.Modules.Impurity F f s,
          AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt I.g I.specialPoint])
