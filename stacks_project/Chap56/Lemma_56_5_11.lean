/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import stacks_project.Chap56.Lemma_56_5_11_Box
public import stacks_project.Chap56.Lemma_56_5_7_Kernel

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
variable [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
variable [HasInjectiveResolutions (Limits.pullback x y).Modules]

/-- Lemma 56.5.11: in the correspondence of Lemma 56.5.7, if `F` is the
Fourier--Mukai functor associated to an exact kernel `K` and `X` is separated
and flat over `R`, then there is a surjection
`boxProduct x y (structureSheaf X) ((fourierMukai x y K).obj (structureSheaf X)) ⟶ K`. -/
@[stacks 0FZJ]
theorem exists_epi_boxProduct_fourierMukai
    [IsSeparated x] [Flat x]
    (K : Scheme.QCoh (Limits.pullback x y)) [IsExactFourierMukaiKernel x y K] :
    ∃ φ : boxProduct x y (structureSheaf X)
        ((fourierMukai x y K).obj (structureSheaf X)) ⟶ K,
      Epi φ := sorry

end AlgebraicGeometry.Scheme.QCoh
