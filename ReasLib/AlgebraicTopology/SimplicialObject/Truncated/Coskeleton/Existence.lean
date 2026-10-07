module

public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteConnected
public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Adjunction
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 09VS

# Existence of coskeleton functors under minimal limit assumptions

The positive-degree construction is supplied by finite connected matching limits. In degree zero,
binary products alone construct a right adjoint to truncation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- Remark 14.19.11 (1) (09VS): binary products suffice for the existence of a right adjoint to
zero-truncation. -/
@[stacks 09VS "zero coskeleton from binary products"]
noncomputable instance truncation.zero.isLeftAdjoint [HasBinaryProducts C] :
    (truncation 0 : SimplicialObject C ⥤ SimplicialObject.Truncated C 0).IsLeftAdjoint := sorry

end CategoryTheory.SimplicialObject
