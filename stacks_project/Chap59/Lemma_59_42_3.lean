/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyA
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 59.42.3 -/
@[stacks 04DM]
#check (AlgebraicGeometry.hasPropertyA_of_isIntegralHom :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f],
    AlgebraicGeometry.hasPropertyA f)
