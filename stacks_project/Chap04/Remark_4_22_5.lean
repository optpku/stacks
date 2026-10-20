/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pro.Presentation
import StacksCheckRecall

@[expose] public section

universe u v uI vI uJ vJ

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]
variable (I : Type uI) [Category.{vI} I] [Small.{v} I] [LocallySmall.{v} I]
  [IsCofiltered I]
variable (J : Type uJ) [Category.{vJ} J] [Small.{v} J] [LocallySmall.{v} J]
  [IsCofiltered J]
variable (F : I ⥤ C) (G : J ⥤ C)

/- Remark 4.22.5 (1): `Pro C` is the category of pro-objects. -/
@[stacks 05PX "the category of pro-objects"]
#check (Pro C : Type (max u (v + 1)))

/- Remark 4.22.5 (2): `Pro.yoneda` embeds constant systems. -/
@[stacks 05PX "the constant-system embedding"]
#check (Pro.yoneda (C := C) : C ⥤ Pro C)

/- Remark 4.22.5 (3): the constant-system embedding is fully faithful. -/
@[stacks 05PX "full faithfulness of the constant-system embedding"]
#check (Pro.yoneda.fullyFaithful (C := C) : (Pro.yoneda (C := C)).FullyFaithful)

/- Remark 4.22.5 (4): cofiltered diagrams determine pro-objects through `Pro.lim`. -/
@[stacks 05PX "cofiltered diagrams as pro-objects"]
#check (Pro.lim (C := C) I : (I ⥤ C) ⥤ Pro C)

/- Remark 4.22.5 (5): morphisms of presented pro-objects satisfy the limit-colimit formula. -/
@[stacks 05PX "the limit-colimit formula for morphisms of pro-objects"]
#check (Pro.limHomEquiv F G :
  ((Pro.lim I).obj F ⟶ (Pro.lim J).obj G) ≃
    Limits.limit (G.op.op ⋙ Limits.colimit (F.op ⋙ yoneda)))

/- Remark 4.22.5 (6): essential constancy is equivalent to being a constant pro-object. -/
@[stacks 05PX "essentially constant diagrams as constant pro-objects"]
#check (IsCofiltered.isEssentiallyConstant.iff_exists_limIsoYoneda F :
  IsCofiltered.IsEssentiallyConstant F ↔
    ∃ X : C, Nonempty ((Pro.lim I).obj F ≅ Pro.yoneda.obj X))

end CategoryTheory
