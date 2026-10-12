/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver

/-!
# Points of an algebraic space

The public field-valued points, common-extension relation, quotient and induced
maps are owned by `ReasLib.AlgebraicGeometry.AlgebraicSpace.Points`.
This module preserves the original chapter import surface.
-/

@[expose] public section

-- Preserve the field-projection registration of the original chapter module.
attribute [instance] AlgebraicGeometry.AlgebraicSpace.FieldValuedPoint.field
