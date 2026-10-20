/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing.Flat
import StacksCheckRecall

/-!
# Flatness of the morphism from a versal ring

In Situation 107.2.1, the morphism `Spec(A) ⟶ X` of Remark 107.2.9 attached to
a versal ring at a finite-type field-valued point is a flat morphism of
algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open GroupoidsOver
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 107.2.10: In Situation 107.2.1 let `x0 : Spec(k) ⟶ X` be a morphism,
where `k` is a finite type field over `S`. Let `A` be a versal ring to `X` at
`x0`. Then the morphism `Spec(A) ⟶ X` of Remark 107.2.9 is flat.
For `hx : RealizesVersalRing x0 A x`, the proof `hx.2.2` supplies formal
versality of the actual restriction, and `hx.1` identifies `x.base = A`. -/
@[stacks 0DR2]
#check (AlgebraicGeometry.AlgebraicStack.isFlat_yonedaOfObject :
    {S : Scheme.{u}} → [IsLocallyNoetherian S] →
    {X : GroupoidsOver S} → [AlgebraicStack X] →
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)] →
    (x : CompleteLocalObject X) →
    [hversal : GroupoidsOver.FormalObject.IsVersal (FormalObject.restriction x)] →
    Flat (yonedaOfObject x.base.toS x.object x.over_obj))

end AlgebraicGeometry.AlgebraicStack
