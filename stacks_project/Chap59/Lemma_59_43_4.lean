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

/- Lemma 59.43.4: an integral morphism of schemes has property (B). -/
@[stacks 04DR] #check (AlgebraicGeometry.hasPropertyB_of_isIntegralHom :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f], AlgebraicGeometry.hasPropertyB f)
