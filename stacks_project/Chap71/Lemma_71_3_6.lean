module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap71.Lemma_71_2_3_WeaklyAssociated

/-!
# Lemma 71.3.6

A point is weakly associated to the pullback of a quasi-coherent module along
a finite flat morphism of algebraic spaces if and only if its image is weakly
associated to the original module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 71.3.6: for a scheme `S`, a finite flat morphism `f : X ⟶ Y` of
algebraic spaces over `S`, and a quasi-coherent `𝒪_Y`-module `𝒢`, a point `x`
of `X` is weakly associated to `(pullback f).obj 𝒢` if and only if its image is
weakly associated to `𝒢`. -/
@[stacks 0CUT]
theorem mem_weakAss_pullback_iff_of_isFinite_of_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsFinite f] [Flat f] (𝒢 : Y.Modules) [𝒢.IsQuasicoherent] (x : Points X) :
    x ∈ ((pullback f).obj 𝒢).weakAss ↔ Points.map f x ∈ 𝒢.weakAss :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
