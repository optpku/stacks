/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.BoxProduct
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.ExactKernel
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

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

/-- An exact Fourier–Mukai kernel over an affine base, with quasi-compact source
having affine diagonal and separated flat structure morphism, is a quotient of
the external product of the structure sheaf with its Fourier–Mukai transform. -/
theorem exists_epi_boxProduct_fourierMukai
    [IsSeparated x] [Flat x]
    (K : Scheme.QCoh (Limits.pullback x y)) [IsExactFourierMukaiKernel x y K] :
    ∃ φ : boxProduct x y (structureSheaf X)
        ((fourierMukai x y K).obj (structureSheaf X)) ⟶ K,
      Epi φ := sorry

end AlgebraicGeometry.Scheme.QCoh
