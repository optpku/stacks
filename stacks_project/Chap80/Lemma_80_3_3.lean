/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable
import StacksCheckRecall

/-!
# Base change of morphisms representable by algebraic spaces

The property of being representable by algebraic spaces is stable under
base change of presheaves on schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 80.3.3: let `S` be a scheme. For a fibre square of presheaves on
`(Sch/S)_fppf`, if `a : F ⟶ G` is representable by algebraic spaces then so is
its base change `a' : G' ×_G F ⟶ G'`. -/
@[stacks 03Y0] #check (AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces.isStableUnderBaseChange : ∀ {S : AlgebraicGeometry.Scheme.{u}}, CategoryTheory.MorphismProperty.IsStableUnderBaseChange (@AlgebraicGeometry.AlgebraicSpace.representableByAlgebraicSpaces S))

end AlgebraicGeometry.AlgebraicSpace
