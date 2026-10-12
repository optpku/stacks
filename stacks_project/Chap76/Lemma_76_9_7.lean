/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_9_7_SquareZero

/-!
# First-order thickenings from square-zero algebras on algebraic spaces

A locally surjective square-zero extension of `𝒪_X` on `X_étale` with quasi-coherent
kernel is realized by a first-order thickening over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open SheafOfModules.RingedSite
open AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension

/-- Lemma 76.9.7: Let `S` be a scheme. Let `f : X ⟶ B` be a morphism of algebraic
spaces over `S`. Given a locally surjective square-zero extension
`π : A ⟶ 𝒪_X` of `f⁻¹𝒪_B`-algebras on `X_étale` whose kernel is quasi-coherent as
an `𝒪_X`-module, there exists a first-order thickening `i : X ⟶ X'` over `B` and
an isomorphism `i⁻¹𝒪_{X'} ⟶ A` of `f⁻¹𝒪_B`-algebras compatible with the
surjections to `𝒪_X`. -/
@[stacks 05ZT]
theorem exists_firstOrderThickening {S : Scheme.{u}} {B X : AlgebraicSpace S}
    (f : X ⟶ B) (A : Sheaf (smallEtaleTopology X) CommRingCat.{u})
    (π : A ⟶ commStructureSheaf X) [Sheaf.IsLocallySurjective π]
    (hπ : KernelIdeal.IsSquareZero π) [(kernelModule π hπ).IsQuasicoherent]
    (α : commInverseImageStructureSheaf f ⟶ A)
    (hα : α ≫ π = commInverseImageStructureSheafMap f) :
    ∃ (X' : AlgebraicSpace S) (i : X ⟶ X') (s' : X' ⟶ B)
      (φ : commInverseImageStructureSheaf i ⟶ A),
      IsRealization f A π hπ α hα i s' φ :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.SquareZeroExtension
