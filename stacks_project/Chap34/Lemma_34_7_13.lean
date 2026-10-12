/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.Big
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

universe u

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {X Y Z : Over S} (f : X ⟶ Y) (g : Y ⟶ Z)

/-!
# Lemma 34.7.13

The bundled big fppf morphism of topoi and its composition law are owned by
`AlgebraicGeometry.Scheme.Fppf.Big`; this chapter item is a canonical recall
of those reusable declarations.
-/

/- Lemma 34.7.13: big fppf morphisms of topoi compose along composition of morphisms over `S`. -/
@[stacks 021X] #check
  (AlgebraicGeometry.Scheme.Fppf.Big.morphismOfTopoi_comp f.left g.left :
    MorphismOfTopoiIn.comp
      (AlgebraicGeometry.Scheme.Fppf.Big.morphismOfTopoi g.left)
      (AlgebraicGeometry.Scheme.Fppf.Big.morphismOfTopoi f.left) =
      AlgebraicGeometry.Scheme.Fppf.Big.morphismOfTopoi (f.left ≫ g.left))

end AlgebraicGeometry
