module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_45_2_Integral

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 74.6.6: for a finite morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, a quasi-coherent `𝒪_X`-module `ℱ` is of finite type if and only if
`(pushforward f).obj ℱ` is of finite type as an `𝒪_Y`-module. -/
@[stacks 060Z]
theorem isFiniteType_iff_pushforward_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ℱ.IsFiniteType ↔ ((pushforward f).obj ℱ).IsFiniteType :=
  sorry

/-- Pushforward along a finite morphism preserves finite type of a
quasi-coherent module on an algebraic space. -/
instance pushforward_obj_isFiniteType_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] :
    ((pushforward f).obj ℱ).IsFiniteType :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
