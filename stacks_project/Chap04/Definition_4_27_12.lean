/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFraction
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (S : MorphismProperty C) [S.HasRightCalculusOfFractions]
variable {X X' Y : C} (f : X' ⟶ Y) (s : X' ⟶ X) (hs : S s)

/- A right fraction is the one-step generalized morphism used by the source. Mathlib owns its
concrete roof as `RightFraction.mk`; ReasLib's `RightFraction.mapQ` specializes its general
evaluation API to the canonical localization `S.Q`, without making callers pass its inversion
proof explicitly. The paper notation `f s⁻¹` suppresses the proof `hs : S s`; no notation is
introduced because this proof and the left/right convention are semantically relevant. -/

/- Definition 4.27.12: for `f : X' ⟶ Y` and `s : X' ⟶ X` with `S s`, the equivalence class
of the roof `(f, s)` is the canonical morphism from `X` to `Y` in `S⁻¹ C`. -/
@[stacks 0BM3 "right fraction represented by a roof"]
#check ((RightFraction.mk s hs f).mapQ : S.Q.obj X ⟶ S.Q.obj Y)

end MorphismProperty
end CategoryTheory
