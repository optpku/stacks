module

public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import ReasLib.CategoryTheory.Functor.Lift.AddCommGrp

/-!
# Additive commutative group structures on type-valued sheafifications

This module records the source-facing compatibility statement for the type-valued
sheafification of an additive-commutative-group-valued presheaf. The canonical additive
sheafification itself remains mathlib's `presheafToSheaf` construction.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u w

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasWeakSheafify J (Type w)] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- The type-valued sheafification of an additive-commutative-group-valued presheaf has a unique
compatible additive commutative group structure for which the sheafification map is additive. -/
theorem existsUniqueCompatibleAddCommGroupStructure_sheafify
    [J.HasSheafCompose (forget AddCommGrpCat.{w})]
    [J.PreservesSheafification (forget AddCommGrpCat.{w})]
    (ℱ : Cᵒᵖ ⥤ AddCommGrpCat.{w}) :
    ∃! h : CompatibleAddCommGroupStructure
        (CategoryTheory.sheafify J (ℱ ⋙ forget AddCommGrpCat.{w})),
      Presheaf.IsSheaf J h.toAddCommGrpCat ∧
        ∃ η : ℱ ⟶ h.toAddCommGrpCat,
          Functor.whiskerRight η (forget AddCommGrpCat.{w}) ≫
              eqToHom h.toAddCommGrpCat_forget =
            CategoryTheory.toSheafify J (ℱ ⋙ forget AddCommGrpCat.{w}) := sorry

end CategoryTheory.GrothendieckTopology
