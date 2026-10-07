module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 74.6.7: for a finite morphism of finite presentation `f : X ⟶ Y` of
algebraic spaces over a scheme `S`, a quasi-coherent `𝒪_X`-module `ℱ` is of
finite presentation if and only if `(pushforward f).obj ℱ` is of finite
presentation as an `𝒪_Y`-module. -/
@[stacks 0610]
theorem isFinitePresentation_iff_pushforward_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] [FinitePresentation f] (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    ℱ.IsFinitePresentation ↔ ((pushforward f).obj ℱ).IsFinitePresentation :=
  sorry

/-- Pushforward along a finite morphism of finite presentation preserves finite
presentation of a quasi-coherent module on an algebraic space. -/
instance pushforward_obj_isFinitePresentation_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] [FinitePresentation f] (ℱ : X.Modules)
    [ℱ.IsQuasicoherent] [ℱ.IsFinitePresentation] :
    ((pushforward f).obj ℱ).IsFinitePresentation :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
