/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

@[expose] public section

open CategoryTheory Limits

universe u v

namespace CategoryTheory.Mono

/-- The second projection of a pullback of a monomorphism is a monomorphism. -/
theorem pullbackSnd {C : Type u} [Category.{v} C] {X Y Z : C}
    (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] [Mono f] :
    Mono (pullback.snd f g) := CategoryTheory.Limits.pullback.snd_of_mono

end CategoryTheory.Mono
