module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

/-!
# Finite presentation over a quasi-compact quasi-separated algebraic space
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.28.8: Let `S` be a scheme. Let `Y` be an algebraic space over `S`
which is quasi-compact and quasi-separated. If `X` is of finite presentation
over `Y`, then `X` is quasi-compact and quasi-separated. -/
@[stacks 06G5] #check
  (AlgebraicGeometry.AlgebraicSpace.isQuasiCompact_and_isQuasiSeparated_of_finitePresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [IsQuasiCompact Y] → [IsAbsolutelyQuasiSeparated Y] → [FinitePresentation f] →
        IsQuasiCompact X ∧ IsAbsolutelyQuasiSeparated X)

end AlgebraicGeometry.AlgebraicSpace
