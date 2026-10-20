module

public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.CategoryTheory.Sites.Sheafification

@[expose] public section

universe u v

namespace CategoryTheory

open Limits

/-- Abelian-group-valued presheaves on any site admit weak sheafification at the
universe of the site's objects and morphisms. -/
instance (priority := 2000) hasWeakSheafify_addCommGrp
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    HasWeakSheafify J AddCommGrpCat.{max u v} := by
  let hcolim : ∀ U : C,
      PreservesColimitsOfShape (J.Cover U)ᵒᵖ
        (forget AddCommGrpCat.{max u v}) := fun U ↦
    @PreservesFilteredColimitsOfSize.preserves_filtered_colimits _ _ _ _
      (forget AddCommGrpCat.{max u v}) inferInstance _ _
      (@isFiltered_op_of_isCofiltered _ _
        (isCofiltered_of_semilatticeInf_nonempty (J.Cover U)))
  exact (@plusPlusAdjunction _ _ J AddCommGrpCat.{max u v}
    _ _ _ _ _ _ _ _ hcolim _).isRightAdjoint

end CategoryTheory
