/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_45_2_Integral

/-!
# Lemma 69.17.3

A finite surjective morphism of algebraic spaces from an affine source onto a
Noetherian target forces the target to be affine.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.17.3: if `f : Y ⟶ X` is a finite surjective morphism of algebraic
spaces over a scheme `S`, `Y` is affine, and `X` is Noetherian, then `X` is
affine. -/
@[stacks 07VP]
theorem isAffine_of_isFinite_surjective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [IsFinite f] [Surjective f] [IsAffine Y] [IsNoetherian X] : IsAffine X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
