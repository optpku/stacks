/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Abelian.GrothendieckAxioms.GabrielPopescu
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory.IsGrothendieckAbelian.GabrielPopescu

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
variable {U A : C} {M : ModuleCat (End U)ᵐᵒᵖ}

/- Lemma 19.14.2: for a separator `U`, the adjoint transpose of a monomorphism
`M ⟶ (preadditiveCoyonedaObj U).obj A` is a monomorphism. -/
@[stacks 0F5T] #check
  fun (hU : IsSeparator U)
      {f : M ⟶ (preadditiveCoyonedaObj U).obj A} [Mono f] ↦
    (adjointMap_mono hU :
      Mono (((tensorObjPreadditiveCoyonedaObjAdjunction U).homEquiv M A).symm f))

end CategoryTheory.IsGrothendieckAbelian.GabrielPopescu
