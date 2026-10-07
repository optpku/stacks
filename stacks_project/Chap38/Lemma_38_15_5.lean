module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.Etale

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 38.15.5: under Situation 38.15.1, if an impurity of `F` above `s` has
a base-change morphism finite type and quasi-finite at its special point, then `F` has
an impurity above `s` whose pointed base change is an elementary étale neighbourhood. -/
@[stacks 05J0] #check
  (AlgebraicGeometry.Scheme.Modules.Impurity.exists_elementary_of_quasiFiniteAt :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [AlgebraicGeometry.Scheme.Hom.FiniteType f]
      [F.IsQuasicoherent] [F.IsFiniteType] (s : S),
      (∃ I : AlgebraicGeometry.Scheme.Modules.Impurity F f s,
        AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt I.g I.specialPoint) →
      ∃ I : AlgebraicGeometry.Scheme.Modules.Impurity F f s, I.IsElementary)
