/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.QuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Impurity

/- Lemma 38.15.6: under Situation 38.15.1 and local Noetherianity of `S`, an
impurity above `s` admits a refinement whose base-change morphism is finite type
and quasi-finite at its special point. -/
@[stacks 05J1] #check
  (AlgebraicGeometry.Scheme.Modules.Impurity.exists_quasiFiniteAt :
    ∀ {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
      [IsLocallyNoetherian S] (s : S), Nonempty (Impurity F f s) →
        ∃ I : Impurity F f s, Hom.FiniteType.QuasiFiniteAt I.g I.specialPoint)

end AlgebraicGeometry.Scheme.Modules.Impurity
