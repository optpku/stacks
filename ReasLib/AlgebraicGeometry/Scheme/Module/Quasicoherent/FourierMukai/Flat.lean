module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Admissible
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}}

/-- Exactness of the Fourier--Mukai transform of a kernel on an affine source
implies that the kernel is flat over the source. -/
theorem fourierMukai_flatOver_of_exact
    (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R)) [IsAffine X]
    (K : Scheme.QCoh (Limits.pullback x y))
    (hF : exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) (fourierMukai x y K)) :
    Scheme.Modules.flatOver K.obj (Limits.pullback.fst x y) :=
  sorry

/-- A kernel corresponding to an exact admissible Fourier--Mukai functor is flat
over the source. -/
theorem fourierMukaiKernel_flatOver_of_exact
    (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R))
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) [Admissible x y F]
    (hF : exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) F)
    (K : Scheme.QCoh (Limits.pullback x y))
    (t : F ⟶ fourierMukai x y K)
    (hlocal : ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsAffine X'],
      IsIso (Functor.whiskerLeft (Scheme.QCoh.pushforward f) t)) :
    Scheme.Modules.flatOver K.obj (Limits.pullback.fst x y) :=
  sorry

end AlgebraicGeometry.Scheme.QCoh
