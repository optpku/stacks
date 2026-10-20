module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.ExactKernel
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.Naturality

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

/-- The functor sending an exact Fourier--Mukai kernel to its exact, relatively
`R`-linear, coproduct-preserving Fourier--Mukai functor. -/
def exactFourierMukai :
    exactFourierMukaiKernel x y ⥤ ExactCoproductLinearFunctor x y where
  obj K := ⟨fourierMukai x y K.obj, exactAdmissible_fourierMukai_of_mem x y K⟩
  map {K K'} α := ObjectProperty.homMk (fourierMukaiHom x y α.hom)
  map_id := by
    intro K
    apply ObjectProperty.hom_ext
    exact fourierMukaiHom_id x y K.obj
  map_comp := by
    intro K K' K'' α β
    apply ObjectProperty.hom_ext
    exact fourierMukaiHom_comp x y α.hom β.hom

/-- The underlying functor assigned to a kernel by `exactFourierMukai` is its
Fourier--Mukai transform. -/
theorem exactFourierMukai_obj (K : exactFourierMukaiKernel x y) :
    ((exactFourierMukai x y).obj K).obj = fourierMukai x y K.obj := rfl

/-- For a quasi-compact source scheme with affine diagonal, Fourier--Mukai
transforms give an equivalence between kernels flat over the source with
vanishing positive higher direct images for every quasicoherent input, and
exact relatively `R`-linear functors preserving arbitrary coproducts. -/
@[stacks 0FZH]
instance exactFourierMukai_isEquivalence :
    (exactFourierMukai x y).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.QCoh
