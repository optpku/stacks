module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.AffineOpenCoproductLinear
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.Naturality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal

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

/-- Every Fourier–Mukai functor from a quasi-compact scheme with affine diagonal is
affine-open coproduct-linear over the affine base. -/
instance fourierMukai_affineOpenCoproductLinear
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (K : Scheme.QCoh (Limits.pullback x y)) :
    AffineOpenCoproductLinear x y (fourierMukai x y K) := sorry

/-- An affine-open coproduct-linear functor from a quasi-compact scheme with affine diagonal
admits a quasicoherent kernel and an invertible comparison transformation to its Fourier–Mukai
functor. -/
theorem exists_fourierMukai_iso_of_affineOpenCoproductLinear
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) [AffineOpenCoproductLinear x y F] :
    ∃ (K : Scheme.QCoh (Limits.pullback x y)) (t : F ⟶ fourierMukai x y K),
      IsIso t := sorry

/-- The kernel assignment sending a quasicoherent module on the fiber product to its
Fourier–Mukai functor, viewed as an affine-open coproduct-linear functor. -/
def affineOpenFourierMukai
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    Scheme.QCoh (Limits.pullback x y) ⥤ AffineOpenCoproductLinearFunctor x y where
  obj K := ⟨fourierMukai x y K, inferInstance⟩
  map {K K'} α := ObjectProperty.homMk (fourierMukaiHom x y α)
  map_id := by
    intro K
    apply ObjectProperty.hom_ext
    exact fourierMukaiHom_id x y K
  map_comp := by
    intro K K' K'' α β
    apply ObjectProperty.hom_ext
    exact fourierMukaiHom_comp x y α β

/-- The underlying functor assigned to a kernel is its Fourier–Mukai functor. -/
theorem affineOpenFourierMukai_obj
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (K : Scheme.QCoh (Limits.pullback x y)) :
    ((affineOpenFourierMukai x y).obj K).obj = fourierMukai x y K := rfl

/-- For a quasi-compact source scheme with affine diagonal, the kernel assignment is an
equivalence between quasicoherent kernels and affine-open coproduct-linear functors. -/
instance affineOpenFourierMukai_isEquivalence
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))] :
    (affineOpenFourierMukai x y).IsEquivalence := sorry

end AlgebraicGeometry.Scheme.QCoh
