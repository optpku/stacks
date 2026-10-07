module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated

/-!
# Lemma 71.3.1

The weakly associated locus of the pushforward of a quasi-coherent module along
an affine morphism of algebraic spaces is contained in the image of the weakly
associated locus of that module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 71.3.1: Let `S` be a scheme. Let `f : X ⟶ Y` be an affine morphism of
algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. Then
`((pushforward f).obj F).weakAss ⊆ Points.map f '' F.weakAss`. -/
@[stacks 0CU2]
theorem weakAss_pushforward_subset_image_of_affine
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).weakAss ⊆ Points.map f '' F.weakAss :=
  sorry

/-- A point of `|Y|` that is weakly associated to the affine pushforward of a
quasi-coherent module is the image of a weakly associated point of that
module. -/
theorem mem_weakAss_pushforward_subset_of_affine
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    (F : X.Modules) [F.IsQuasicoherent] (y : Points Y) :
    y ∈ ((pushforward f).obj F).weakAss →
      ∃ x : Points X, x ∈ F.weakAss ∧ Points.map f x = y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
