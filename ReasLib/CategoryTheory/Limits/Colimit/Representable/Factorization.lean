module

public import ReasLib.CategoryTheory.Limits.Colimit.Representable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Factorization through stages of a colimit

This leaf identifies the image of the canonical representable-colimit comparison with the
morphisms that factor through one object of the diagram.  The formulation works in an arbitrary
category and does not require the indexing category to be filtered.
-/

@[expose] public section

open CategoryTheory Opposite

universe v u

namespace CategoryTheory.Limits.colimitPost

variable {J : Type v} [SmallCategory J]
variable {C : Type u} [Category.{v} C]

/-- A morphism into a colimit factors through a single stage of the diagram. -/
@[stacks 05NN "factorization through a colimit stage"]
def FactorsThroughStage {A : C} (B : J ⥤ C) [HasColimit B]
    (f : A ⟶ colimit B) : Prop :=
  ∃ (j : J) (g : A ⟶ B.obj j), g ≫ colimit.ι B j = f

/-- The composite of a morphism to a diagram object with its colimit coprojection factors
through that stage. -/
theorem factorsThroughStage_ι {A : C} (B : J ⥤ C) [HasColimit B]
    (j : J) (g : A ⟶ B.obj j) :
    FactorsThroughStage B (g ≫ colimit.ι B j) := sorry

/-- A morphism lies in the image of the representable-colimit comparison exactly when it
factors through one stage of the diagram. -/
@[stacks 05NN "range of the representable-colimit comparison"]
theorem mem_range_iff_factorsThroughStage (A : C) (B : J ⥤ C) [HasColimit B]
    (f : A ⟶ colimit B) :
    f ∈ Set.range (colimit.post B (coyoneda.obj (op A))) ↔
      FactorsThroughStage B f := sorry

/-- The representable-colimit comparison is surjective exactly when every morphism into the
colimit factors through one stage. -/
theorem surjective_iff_forall_factors (A : C) (B : J ⥤ C) [HasColimit B] :
    Function.Surjective (colimit.post B (coyoneda.obj (op A))) ↔
      ∀ f : A ⟶ colimit B, FactorsThroughStage B f := sorry

/-- A morphism into a colimit that does not factor through any stage witnesses failure of
surjectivity of the representable-colimit comparison. -/
theorem not_surjective_of_not_factors (A : C) (B : J ⥤ C) [HasColimit B]
    (f : A ⟶ colimit B) (hf : ¬ FactorsThroughStage B f) :
    ¬ Function.Surjective (colimit.post B (coyoneda.obj (op A))) := sorry

/-- If the target Hom-set of a representable-colimit comparison is subsingleton, any two
distinct elements of its source witness failure of injectivity. -/
theorem not_injective_of_subsingleton (A : C) (B : J ⥤ C) [HasColimit B]
    [Subsingleton (A ⟶ colimit B)]
    {x y : colimit (B ⋙ coyoneda.obj (op A))} (hxy : x ≠ y) :
    ¬ Function.Injective (colimit.post B (coyoneda.obj (op A))) := sorry

end CategoryTheory.Limits.colimitPost
