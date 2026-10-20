module

public import stacks_project.Chap88.Definition_88_21_1_Formal

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Affine

/-!
# Affine formal algebraic spaces

An affine formal algebraic space over `S` is a directed affine thickening
colimit of schemes over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.FormalAlgebraicSpace.IsAffine :
  ∀ {S : Scheme.{u}}, ((Over S)ᵒᵖ ⥤ Type u) → Prop)
