/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.FreeAbelian
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {I : Type w}
variable (G : I → Cᵒᵖ ⥤ Type (max u v w))

/- Lemma 18.4.3 (03A9): free abelian presheaves preserve arbitrary coproducts. -/
@[stacks 03A9]
#check (FreeAbelianPresheaf.coproductIso G :
  FreeAbelianPresheaf.obj (∐ G) ≅ ∐ fun i ↦ FreeAbelianPresheaf.obj (G i))

end CategoryTheory
