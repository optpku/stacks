/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 58.17.5: if a closed immersion meets every connected component of the
base, restriction of finite étale schemes is faithful. -/
@[stacks 0EJX] #check
  (AlgebraicGeometry.Scheme.finiteEtaleBaseChange_faithful_of_meetsConnectedComponents :
    ∀ {X Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i]
      [Fact (∀ x : X, ∃ y : Y, i y ∈ connectedComponent x)],
      (AlgebraicGeometry.Scheme.finiteEtaleBaseChange i).Faithful)

end AlgebraicGeometry.Scheme
