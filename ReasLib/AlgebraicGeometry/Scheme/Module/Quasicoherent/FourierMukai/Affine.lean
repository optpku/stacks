/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Admissible
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.Naturality

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))

/-- If `X` is affine, then the second projection of `Limits.pullback x y` is an
affine morphism. -/
instance isAffineHom_pullback_snd [IsAffine X] :
    IsAffineHom (Limits.pullback.snd x y) :=
  MorphismProperty.pullback_snd x y (isAffineHom_of_isAffine x)

/-- Fourier--Mukai functors associated to kernels on `Limits.pullback x y` are
admissible when `X` is affine. -/
instance fourierMukai_admissible [IsAffine X]
    (K : Scheme.QCoh (Limits.pullback x y)) :
    Admissible x y (Scheme.QCoh.fourierMukai x y K) := sorry

/-- The functor sending a quasicoherent kernel on `Limits.pullback x y` to the
corresponding Fourier--Mukai functor, viewed as an admissible functor. -/
def admissibleFourierMukai [IsAffine X] :
    Scheme.QCoh (Limits.pullback x y) ⥤ RightExactCoproductLinearFunctor x y where
  obj K := ⟨Scheme.QCoh.fourierMukai x y K, inferInstance⟩
  map {K K'} α := homMk (fourierMukaiHom x y α)
  map_id := by
    intro K
    apply ObjectProperty.hom_ext
    exact fourierMukaiHom_id x y K
  map_comp := by
    intro K K' K'' α β
    apply ObjectProperty.hom_ext
    exact fourierMukaiHom_comp x y α β

/-- The underlying functor of `admissibleFourierMukai` is the Fourier--Mukai
functor associated to its kernel. -/
theorem admissibleFourierMukai_obj [IsAffine X]
    (K : Scheme.QCoh (Limits.pullback x y)) :
    ((admissibleFourierMukai x y).obj K).obj = fourierMukaiFunctor x y K := sorry

/-- For an affine source, the kernel-to-Fourier--Mukai functor is an
equivalence between quasicoherent kernels and admissible functors. -/
instance fourierMukai_isEquivalence [IsAffine X] :
    (admissibleFourierMukai x y).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.QCoh
