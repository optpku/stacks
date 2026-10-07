module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap76.Definition_76_7_2_Differentials

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Lemma 76.7.14: let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S`. If `f` is locally of finite type, then `Ω[f]` is a finite type `𝒪_X`-module. -/
@[stacks 05ZE]
instance isFiniteType_relativeDifferentials_of_locallyOfFiniteType
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AlgebraicSpace.LocallyOfFiniteType f] :
    (relativeDifferentials f).IsFiniteType :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
