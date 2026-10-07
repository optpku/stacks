module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import stacks_project.Chap56.«56_5_1_1_FourierMukai»
public import stacks_project.Chap56.Lemma_56_5_5
public import stacks_project.Chap56.Lemma_56_5_7_ExactAdmissible

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
          IsZero (higherDirectImage_tensor x y K F q) := sorry

/-- Vanishing of `R^q pr_{2,*}(pr₁^* F ⊗ K)` for `q > 0` on an exact Fourier--Mukai
kernel. -/
theorem higherDirectImage_tensor_isZero (K : Scheme.QCoh (Limits.pullback x y))
    [IsExactFourierMukaiKernel x y K] (F : Scheme.QCoh X) (q : ℕ) (hq : 0 < q) :
    IsZero (higherDirectImage_tensor x y K F q) := sorry

/-- The full subcategory of exact Fourier--Mukai kernels on `Limits.pullback x y`. -/
abbrev exactFourierMukaiKernel :=
  ObjectProperty.FullSubcategory
    fun K : Scheme.QCoh (Limits.pullback x y) ↦ IsExactFourierMukaiKernel x y K

/-- Fourier--Mukai functors of exact kernels are exact-admissible when `X` is
quasi-compact with affine diagonal. -/
instance fourierMukai_exactAdmissible
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (K : Scheme.QCoh (Limits.pullback x y)) [IsExactFourierMukaiKernel x y K] :
    ExactAdmissible x y (fourierMukai x y K) := sorry

/-- Objects of `exactFourierMukaiKernel` induce exact-admissible Fourier--Mukai
functors when `X` is quasi-compact with affine diagonal. -/
theorem exactAdmissible_fourierMukai_of_mem
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (K : exactFourierMukaiKernel x y) :
    ExactAdmissible x y (fourierMukai x y K.obj) := sorry

end AlgebraicGeometry.Scheme.QCoh
