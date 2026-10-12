/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.InGroupoids.Counterexample.NoLift
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Counterexample.TwoLifts
import StacksCheckRecall

@[expose] public section

namespace CategoryTheory.Functor.IsFibered.InGroupoids.Counterexample

open CategoryTheory.Functor

/- Example 4.35.5 (1): the missing-lift projection has groupoid standard fibres. -/
@[stacks 02C4 "(1)"]
#check (NoLift.fiberIsGroupoid :
  ∀ U : WalkingComposablePair, IsGroupoid (NoLift.projection.Fiber U))

/- Example 4.35.5 (2): `WalkingComposablePair.Hom.f` has no lift from `NoLift.Obj.A'` to
`NoLift.Obj.B'`. -/
@[stacks 02C4 "(2)"]
#check (NoLift.noLiftOfF :
  ¬ ∃ phi : NoLift.Hom NoLift.Obj.A' NoLift.Obj.B',
    NoLift.projection.IsHomLift WalkingComposablePair.Hom.f phi)

/- Example 4.35.5 (3): the competing-lifts projection has groupoid standard fibres. -/
@[stacks 02C4 "(3)"]
#check (TwoLifts.fiberIsGroupoid :
  ∀ U : WalkingComposablePair, IsGroupoid (TwoLifts.projection.Fiber U))

/- Example 4.35.5 (4): `TwoLifts.Hom.f₁` is a lift of the named base arrow. -/
@[stacks 02C4 "(4)"]
#check (TwoLifts.f₁IsHomLift :
  TwoLifts.projection.IsHomLift WalkingComposablePair.Hom.f TwoLifts.Hom.f₁)

/- Example 4.35.5 (5): `TwoLifts.Hom.f₂` is a lift of the named base arrow. -/
@[stacks 02C4 "(5)"]
#check (TwoLifts.f₂IsHomLift :
  TwoLifts.projection.IsHomLift WalkingComposablePair.Hom.f TwoLifts.Hom.f₂)

/- Example 4.35.5 (6): the two named lifts are distinct. -/
@[stacks 02C4 "(6)"]
#check (TwoLifts.f₁_ne_f₂ :
  (TwoLifts.Hom.f₁ : TwoLifts.Hom TwoLifts.Obj.A' TwoLifts.Obj.B') ≠
    TwoLifts.Hom.f₂)

end CategoryTheory.Functor.IsFibered.InGroupoids.Counterexample
