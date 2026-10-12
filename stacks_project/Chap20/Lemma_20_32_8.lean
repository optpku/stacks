/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.ExtensionByZero.Derived
import StacksCheckRecall

@[expose] public section

/- Lemma 20.32.8 (08BT): for an open immersion `j : U ↪ X`, derived restriction
`j^* : D(𝒪_X) ⥤ D(𝒪_U)` is right adjoint to derived extension by zero
`j_! : D(𝒪_U) ⥤ D(𝒪_X)`. -/
@[stacks 08BT "derived restriction is right adjoint to extension by zero"]
#check @AlgebraicGeometry.RingedSpace.OpenSubspace.ExtensionByZero.derivedIsRightAdjoint
