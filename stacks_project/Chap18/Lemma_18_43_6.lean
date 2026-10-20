/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Monoidal
import StacksCheckRecall

/-!
# Lemma 18.43.6

Compatibility facade for the reusable monoidal-closure API for locally constant sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [CommRing Λ]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable [((J.W : MorphismProperty (Cᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]
variable {F G : Sheaf J (ModuleCat.{w} Λ)}
variable [IsLocallyConstant F] [IsLocallyConstant G]

/- Lemma 18.43.6: the canonical tensor product of two locally constant sheaves of
`Λ`-modules is locally constant. -/
@[stacks 093V]
#check (IsLocallyConstant.tensorModule (J := J) (F := F) (G := G) :
  IsLocallyConstant (F ⊗ G))

/- The coefficient-independent owner exposes the same closure for arbitrary compatible monoidal
sheaf, restriction, and constant-sheaf structures. -/
#check @IsLocallyConstant.tensor

/- The object-property form lets downstream monoidal-subcategory constructions consume the
closure fact directly. -/
#check @locallyConstant.tensorLE

end CategoryTheory.Sheaf
