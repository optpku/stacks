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

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Points :
  ∀ {S : AlgebraicGeometry.Scheme.{u}}, AlgebraicGeometry.AlgebraicSpace S → Type (u + 1))
