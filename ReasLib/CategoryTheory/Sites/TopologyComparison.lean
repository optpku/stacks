module

public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Closed
public import Mathlib.CategoryTheory.Sites.Sheaf

/-!
# Comparison of Grothendieck topologies

The order relation between two topologies on one category induces continuous and cocontinuous
identity functors in opposite directions.
-/

@[expose] public section

universe u v

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

/-- The identity functor is continuous from a topology with fewer covering sieves to one with
more covering sieves. -/
theorem id_isContinuous_of_le
    {J J' : GrothendieckTopology C} (h : J' ≤ J) :
    (𝟭 C).IsContinuous J' J := sorry

/-- The identity functor is cocontinuous in the direction opposite a comparison of topologies. -/
theorem id_isCocontinuous_of_le
    {J J' : GrothendieckTopology C} (h : J' ≤ J) :
    (𝟭 C).IsCocontinuous J J' := sorry

end CategoryTheory.Functor

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] {J J' : GrothendieckTopology C}

/-- A comparison of Grothendieck topologies is equivalently the inclusion of their
set-valued sheaf predicates. -/
theorem le_iff_isSheafFor_type :
    J ≤ J' ↔
      ∀ P : Cᵒᵖ ⥤ Type (max u v), Presheaf.IsSheaf J' P → Presheaf.IsSheaf J P := sorry

end CategoryTheory.GrothendieckTopology
