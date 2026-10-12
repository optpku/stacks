/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

/- Lemma 19.14.1: in the Gabriel-Popescu setup for a generator `U`, the functor
`preadditiveCoyonedaObj U : C ⥤ ModuleCat (End U)ᵐᵒᵖ` has a left adjoint
`tensorObj U : ModuleCat (End U)ᵐᵒᵖ ⥤ C`. This is exactly the canonical adjunction
`tensorObjPreadditiveCoyonedaObjAdjunction`. -/
@[stacks 0F5S] #check
  fun (U : C) (_ : IsSeparator U) ↦
    (tensorObjPreadditiveCoyonedaObjAdjunction U :
      tensorObj U ⊣ preadditiveCoyonedaObj U)

end CategoryTheory.IsGrothendieckAbelian
