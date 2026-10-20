module

public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Stalk

/-!
# Dimension under field extension

This file records preservation of the dimension-at-most-one bound for schemes
after extending the base field.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.FieldExtension

variable {k k' : Type u} [Field k] [Field k'] [Algebra k k']
variable {X : Scheme.{u}}

/-- Extending the base field preserves a topological Krull dimension bound of one for schemes
locally of finite type over the original field. -/
theorem topologicalKrullDim_baseChange_le_one
    (f : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType f]
    (hdim : topologicalKrullDim X ≤ 1) :
    topologicalKrullDim (baseChange k k' f) ≤ 1 := sorry

end AlgebraicGeometry.FieldExtension
