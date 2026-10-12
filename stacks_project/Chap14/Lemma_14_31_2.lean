/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.KanFibration
import StacksCheckRecall

/-!
@stack 08NV
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet.modelCategoryQuillen

variable {X Y Y' : SSet.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
variable [Fibration f]

/- Lemma 14.31.2 (08NV): base change preserves Kan fibrations. The required stability is now a
global owner instance rather than a chapter-local reconstruction. -/
@[stacks 08NV]
#check (inferInstance : Fibration (pullback.snd f g))

end SSet.modelCategoryQuillen
