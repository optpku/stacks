module

public import stacks_project.Chap56.Lemma_56_5_10_Triple

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y T : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
variable (t : T ⟶ Spec (CommRingCat.of R))
variable [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
variable [HasInjectiveResolutions (Limits.pullback x y).Modules]
variable [HasInjectiveResolutions (triplePullback x y t).Modules]

/-- Lemma 56.5.10: if `K` is an exact Fourier--Mukai kernel on `X ×_R Y` as in
Lemma 56.5.7 (2), then for every scheme `T` over `R`, every quasicoherent
`F` on `T ×_R X`, and every `q > 0`, the higher direct image
`R^q pr₁₃,*(pr₁₂^* F ⊗ pr₂₃^* K)` on `T ×_R Y` vanishes. -/
@[stacks 0FZI]
theorem higherDirectImage_tripleTensor_isZero
    (K : Scheme.QCoh (Limits.pullback x y)) [IsExactFourierMukaiKernel x y K]
    (F : Scheme.QCoh (Limits.pullback t x)) (q : ℕ) (hq : 0 < q) :
    IsZero (higherDirectImage_tripleTensor x y t K F q) := sorry

end AlgebraicGeometry.Scheme.QCoh
