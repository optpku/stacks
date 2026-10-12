/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Lemma 67.39.3: The composition of two étale morphisms of algebraic spaces is étale. -/
@[stacks 0465] #check
  (AlgebraicGeometry.AlgebraicSpace.Etale.etale_comp :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) {Z : AlgebraicSpace S}
      (g : Y ⟶ Z) [AlgebraicSpace.Etale f] [AlgebraicSpace.Etale g],
      AlgebraicSpace.Etale (f ≫ g))
