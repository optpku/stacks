/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.GradedEquivariant
public import ReasLib.Algebra.Module.Graded.Left.Category
public import stacks_project.Chap39.Definition_39_12_1_Equivariant

/-!
# Compatibility for equivariant affine tilde modules

This module retains the affine tilde equivalence name used by existing source-facing consumers
and re-exports the reusable graded equivariant tilde API.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GradedSpec

/-- The canonical affine tilde equivalence for `Spec A`. -/
abbrev affineTildeEquiv (A : Type u) [CommRing A] :
    ModuleCat A ≌ Scheme.QCoh (Spec (CommRingCat.of A)) :=
  AlgebraicGeometry.tildeEquiv (R := CommRingCat.of A)

variable {A : Type u} [CommRing A] (𝒜 : ℤ → Submodule ℤ A) [GradedAlgebra 𝒜]
  (M : GradedModule.Left.{0, u, u, 0} 𝒜 ℤ)

/- Compatibility check for the equivariant affine tilde module of a graded module. -/
#check (AlgebraicGeometry.GradedSpec.equivariantTilde 𝒜 M :
  Scheme.QCoh.Equivariant MultiplicativeGroup.group
    (AlgebraicGeometry.GradedSpec.action 𝒜))

end AlgebraicGeometry.GradedSpec
