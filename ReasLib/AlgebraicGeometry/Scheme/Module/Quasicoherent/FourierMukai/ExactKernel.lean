/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.ExactAdmissible
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
variable [HasInjectiveResolutions (Limits.pullback x y).Modules]

/-- The underlying module of `pr₁^* F ⊗ K` on `Limits.pullback x y`. -/
noncomputable def tensorPullback (K : Scheme.QCoh (Limits.pullback x y))
    (F : Scheme.QCoh X) : (Limits.pullback x y).Modules :=
  ((tensorRight K).obj ((Scheme.QCoh.pullback (Limits.pullback.fst x y)).obj F)).obj

/-- The higher direct image `R^q pr_{2,*}(pr₁^* F ⊗ K)`. -/
noncomputable def higherDirectImage_tensor (K : Scheme.QCoh (Limits.pullback x y))
    (F : Scheme.QCoh X) (q : ℕ) : Y.Modules :=
  ((Scheme.Modules.pushforward (Limits.pullback.snd x y)).rightDerived q).obj
    (tensorPullback x y K F)

/-- A kernel on `Limits.pullback x y` is an exact Fourier--Mukai kernel when it is
flat over `X` and its higher direct images `R^q pr_{2,*}(pr₁^* F ⊗ K)` vanish for
every quasicoherent `F` and every `q > 0`. -/
class IsExactFourierMukaiKernel (K : Scheme.QCoh (Limits.pullback x y)) : Prop where
  flatOver : Scheme.Modules.flatOver ((inclusion _).obj K) (Limits.pullback.fst x y)
  vanishing : ∀ (F : Scheme.QCoh X) (q : ℕ), 0 < q →
    IsZero (higherDirectImage_tensor x y K F q)

/-- Exact Fourier--Mukai kernels are characterized by flatness over `X` and
vanishing of positive-degree higher direct images of `pr₁^* F ⊗ K`. -/
theorem isExactFourierMukaiKernel_iff (K : Scheme.QCoh (Limits.pullback x y)) :
    IsExactFourierMukaiKernel x y K ↔
      Scheme.Modules.flatOver ((inclusion _).obj K) (Limits.pullback.fst x y) ∧
        ∀ (F : Scheme.QCoh X) (q : ℕ), 0 < q →
          IsZero (higherDirectImage_tensor x y K F q) := by
  constructor
  · intro h
    exact ⟨h.flatOver, h.vanishing⟩
  · rintro ⟨hF, hV⟩
    exact ⟨hF, hV⟩

/-- Positive-degree higher direct images of `pr₁^* F ⊗ K` vanish on an exact
Fourier--Mukai kernel. -/
theorem higherDirectImage_tensor_isZero (K : Scheme.QCoh (Limits.pullback x y))
    [IsExactFourierMukaiKernel x y K] (F : Scheme.QCoh X) (q : ℕ) (hq : 0 < q) :
    IsZero (higherDirectImage_tensor x y K F q) :=
  IsExactFourierMukaiKernel.vanishing F q hq

/-- The full subcategory of exact Fourier--Mukai kernels on `Limits.pullback x y`. -/
abbrev exactFourierMukaiKernel :=
  ObjectProperty.FullSubcategory
    fun K : Scheme.QCoh (Limits.pullback x y) ↦ IsExactFourierMukaiKernel x y K

/-- Fourier--Mukai functors of exact kernels are exact-admissible when `X` is
quasi-compact with affine diagonal. -/
instance fourierMukai_exactAdmissible
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (K : Scheme.QCoh (Limits.pullback x y)) [hK : IsExactFourierMukaiKernel x y K] :
    ExactAdmissible x y (fourierMukai x y K) := sorry

/-- Objects of `exactFourierMukaiKernel` induce exact-admissible Fourier--Mukai
functors when `X` is quasi-compact with affine diagonal. -/
instance exactAdmissible_fourierMukai_of_mem
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (K : exactFourierMukaiKernel x y) :
    ExactAdmissible x y (fourierMukai x y K.obj) :=
  fourierMukai_exactAdmissible x y K.obj (hK := K.property)

end AlgebraicGeometry.Scheme.QCoh
