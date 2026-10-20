/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Topos
import StacksCheckRecall

/-!
# Lemma 18.43.2

Compatibility facade for inverse-image preservation of locally constant sheaves of sets.
-/

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe u₁ u₂ v₁ v₂ w

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
variable [HasWeakSheafify JC (Type w)] [HasWeakSheafify JD (Type w)]
variable [∀ X : C, HasWeakSheafify (JC.over X) (Type w)]
variable [∀ Y : D, HasWeakSheafify (JD.over Y) (Type w)]
variable (f : MorphismOfTopoiIn JD JC)
variable (G : Sheaf JD (Type w)) [Sheaf.IsLocallyConstant G]

/- Lemma 18.43.2: if `f : Sh(C) ⟶ Sh(D)` is a morphism of topoi and `G` is a locally
constant sheaf of sets on `D`, then `(f⁻¹).obj G` is locally constant on `C`. -/
@[stacks 093R]
#check (MorphismOfTopoiIn.inverseImage_isLocallyConstant f G :
  Sheaf.IsLocallyConstant ((f⁻¹).obj G))

/- The predicate-refined owner preserves restrictions on the allowed constant models. -/
#check MorphismOfTopoiIn.inverseImage_isLocallyConstantWith

end CategoryTheory
