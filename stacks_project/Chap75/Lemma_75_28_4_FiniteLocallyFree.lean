/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
public import stacks_project.Chap75.Definition_75_28_1_ResolutionProperty

/-!
# Transfer of the resolution property along finite locally free morphisms

A surjective finite locally free morphism of algebraic spaces transfers the
resolution property from its source to its target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A surjective finite locally free morphism of algebraic spaces transfers the
resolution property from its source to its target. -/
theorem hasResolutionProperty_of_surjective_finiteLocallyFree {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Surjective f] [FiniteLocallyFree f]
    (hX : HasResolutionProperty X) : HasResolutionProperty Y := sorry

end AlgebraicGeometry.AlgebraicSpace
