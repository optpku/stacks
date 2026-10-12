/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension.Proper

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/- Lemma 37.30.5: for a proper morphism of schemes, the target-indexed fibre-dimension function
is upper semicontinuous. -/
@[stacks 0D4I] #check
  (AlgebraicGeometry.Scheme.Hom.upperSemicontinuous_fiberDimension :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f], UpperSemicontinuous f.fiberDimension)

end AlgebraicGeometry.Scheme.Hom
