/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyB
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 59.43.3: a finite morphism of schemes has property (B). -/
@[stacks 04DQ] #check (AlgebraicGeometry.hasPropertyB_of_isFinite :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f], AlgebraicGeometry.hasPropertyB f)
