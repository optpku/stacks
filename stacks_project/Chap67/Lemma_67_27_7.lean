module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite.Immersion

/-!
# Immersions of algebraic spaces are locally quasi-finite
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.27.7: An immersion of algebraic spaces is locally quasi-finite. -/
@[stacks 03XM] #check
  (AlgebraicGeometry.AlgebraicSpace.locallyQuasiFinite_of_isImmersion :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      [IsImmersion f] → LocallyQuasiFinite f)

end AlgebraicGeometry.AlgebraicSpace
