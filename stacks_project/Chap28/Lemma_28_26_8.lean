/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Separated
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 28.26.8: If a scheme admits an ample invertible sheaf, then it is separated. -/
@[stacks 09MP] #check
  (AlgebraicGeometry.Scheme.Modules.isSeparated_of_exists_isAmple :
    ∀ {X : AlgebraicGeometry.Scheme.{u}},
      AlgebraicGeometry.Scheme.Modules.HasAmpleInvertibleModule X → X.IsSeparated)

end
