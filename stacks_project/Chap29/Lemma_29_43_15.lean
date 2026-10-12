/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 29.43.15: projectivity descends across a separated postcomposition. -/
@[stacks 0C4Q] #check
  (AlgebraicGeometry.projective_of_comp_of_isSeparated :
    ∀ {X Y S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
      [AlgebraicGeometry.IsSeparated g],
      AlgebraicGeometry.Projective (f ≫ g) → AlgebraicGeometry.Projective f)
