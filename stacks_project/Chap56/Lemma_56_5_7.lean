module

public import stacks_project.Chap56.Lemma_56_5_2
public import stacks_project.Chap56.Lemma_56_5_7_ExactAdmissible
public import stacks_project.Chap56.Lemma_56_5_7_Kernel

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
variable [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
variable [HasInjectiveResolutions (Limits.pullback x y).Modules]

/-- The functor sending an exact Fourier--Mukai kernel on `Limits.pullback x y`
to the corresponding Fourier--Mukai functor of (56.5.1.1), viewed as an
exact-admissible functor `Scheme.QCoh X ⥤ Scheme.QCoh Y`. -/
@[stacks 0FZH]
def exactFourierMukai :
    exactFourierMukaiKernel x y ⥤ ExactCoproductLinearFunctor x y where
  obj K := ⟨fourierMukai x y K.obj, sorry⟩
  map {K K'} α :=
    ObjectProperty.homMk
      (Functor.whiskerLeft (Scheme.QCoh.pullback (Limits.pullback.fst x y))
        (Functor.whiskerRight (tensorRightHom α.hom)
          (Scheme.QCoh.pushforward (Limits.pullback.snd x y))))
  map_id := sorry
  map_comp := sorry

/-- The underlying functor of `exactFourierMukai` is the Fourier--Mukai functor
of (56.5.1.1). -/
theorem exactFourierMukai_obj (K : exactFourierMukaiKernel x y) :
    ((exactFourierMukai x y).obj K).obj = fourierMukai x y K.obj := sorry

/-- Lemma 56.5.7: if `X` is quasi-compact with affine diagonal, sending a kernel
`K` on `Limits.pullback x y` that is flat over `X` and has vanishing higher
direct images `R^q pr_{2,*}(pr₁^* F ⊗ K)` for `q > 0` to the Fourier--Mukai
functor of (56.5.1.1) is an equivalence between the full subcategory of such
kernels in `Scheme.QCoh (Limits.pullback x y)` and the category of `R`-linear
exact functors `Scheme.QCoh X ⥤ Scheme.QCoh Y` that commute with arbitrary
direct sums. -/
@[stacks 0FZH]
theorem exactFourierMukai_isEquivalence :
    (exactFourierMukai x y).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.QCoh
