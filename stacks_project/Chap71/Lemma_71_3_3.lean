module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated

/-!
# Lemma 71.3.3

The weakly associated locus of a quasi-coherent module is preserved by
pushforward along a finite morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 71.3.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a finite morphism of
algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. Then
`((pushforward f).obj F).weakAss = Points.map f '' F.weakAss`. -/
@[stacks 0CU9]
theorem weakAss_pushforward_eq_image_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).weakAss = Points.map f '' F.weakAss :=
  sorry

/-- A point of `Points Y` is weakly associated to the finite pushforward of a
quasi-coherent module if and only if it is the image of a weakly associated
point of that module. -/
theorem mem_weakAss_pushforward_iff_of_isFinite
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsFinite f]
    (F : X.Modules) [F.IsQuasicoherent] (y : Points Y) :
    y ∈ ((pushforward f).obj F).weakAss ↔
      ∃ x : Points X, x ∈ F.weakAss ∧ Points.map f x = y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
