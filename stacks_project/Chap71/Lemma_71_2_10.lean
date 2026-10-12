/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated

/-!
# Lemma 71.2.10

A point of `|Y|` outside the image of a quasi-compact quasi-separated morphism
of algebraic spaces is not weakly associated to the pushforward of a
quasi-coherent module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 71.2.10: Let `S` be a scheme. Let `f : X ⟶ Y` be a quasi-compact and
quasi-separated morphism of algebraic spaces over `S`. Let `F` be a
quasi-coherent `𝒪_X`-module. Let `y ∈ Points Y` be a point which is not in the
image of `Points.map f`. Then `y` is not weakly associated to
`(pushforward f).obj F`. -/
@[stacks 0CUQ]
theorem not_mem_weakAss_pushforward_of_not_mem_range
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent]
    (y : Points Y) (hy : y ∉ Set.range (Points.map f)) :
    y ∉ ((pushforward f).obj F).weakAss :=
  sorry

/-- The weakly associated locus of the pushforward of a quasi-coherent module
along a quasi-compact quasi-separated morphism of algebraic spaces is contained
in the range of `Points.map f`. -/
theorem weakAss_pushforward_subset_range
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f] (F : X.Modules) [F.IsQuasicoherent] :
    ((pushforward f).obj F).weakAss ⊆ Set.range (Points.map f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
