/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Generator.SubobjectExtension
public import ReasLib.CategoryTheory.Sites.Sheafification.FreeAbelianYoneda.ULift

/-!
# An injectivity criterion for abelian sheaves

The free abelian Yoneda sheaves form the source-facing test family. The public predicate records
extension from their subobjects, while the theorems identify that predicate with the canonical
`Injective` class.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.GrothendieckTopology.FreeAbelianYoneda.ULift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J AddCommGrpCat.{max w v}]

/-- An abelian sheaf has the free-abelian-Yoneda subobject extension property when it has the
generic generator-subobject extension property for every free abelian Yoneda test object. -/
@[stacks 01DO "free-abelian-Yoneda extension property"]
abbrev HasSubobjectExtension (I : Sheaf J AddCommGrpCat.{max w v}) : Prop :=
  ∀ U : C, Generator.HasSubobjectExtension (obj.{w} J U) I

/-- Every injective abelian sheaf has the free-abelian-Yoneda subobject extension property. -/
theorem hasSubobjectExtension_of_injective (I : Sheaf J AddCommGrpCat.{max w v})
    [Injective I] : HasSubobjectExtension J I := sorry

/-- Lemma 19.7.3: the free-abelian-Yoneda subobject extension property implies injectivity. -/
@[stacks 01DO]
theorem injective_of_hasSubobjectExtension (I : Sheaf J AddCommGrpCat.{max w v})
    (hI : HasSubobjectExtension J I) : Injective I := sorry

/-- An abelian sheaf is injective exactly when it has the free-abelian-Yoneda subobject
extension property. -/
theorem injective_iff_hasSubobjectExtension (I : Sheaf J AddCommGrpCat.{max w v}) :
    Injective I ↔ HasSubobjectExtension J I := sorry

end CategoryTheory.GrothendieckTopology.FreeAbelianYoneda.ULift
