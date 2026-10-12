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

/- Lemma 59.42.2 -/
@[stacks 04DL]
#check (AlgebraicGeometry.hasPropertyA_of_separated_locallyQuasiFinite :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsSeparated f] [LocallyQuasiFinite f],
    AlgebraicGeometry.hasPropertyA f)
