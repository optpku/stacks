/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection
import StacksCheckRecall

/-!
# Definition 31.14.6

A regular global section is one whose associated morphism from the structure sheaf is a
monomorphism.

@stack 01WY
-/

@[expose] public section

/- Definition 31.14.6
For a locally ringed space `X`, an invertible sheaf `ℒ` on `X`, and a global section `s` of `ℒ`,
the section `s` is regular when the induced morphism from the structure module to `ℒ`, sending
`f` to `f * s`, is a monomorphism (equivalently, injective).
-/
@[stacks 01WY] #check (AlgebraicGeometry.RingedSpace.IsRegularSection :
  ∀ {X : AlgebraicGeometry.RingedSpace}, (ℒ : X.Modules) → ℒ.sections → Prop)
