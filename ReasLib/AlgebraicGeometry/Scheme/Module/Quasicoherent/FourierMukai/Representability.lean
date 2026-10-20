module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Admissible
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {R : Type u} [CommRing R]
variable {X Y : Scheme.{u}}
variable (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
variable [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
variable (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) [Admissible x y F]

/-- An admissible functor of quasicoherent modules from a quasi-compact scheme
with affine diagonal admits a quasicoherent kernel on the fibre product and a
natural transformation to its Fourier–Mukai functor, which becomes an
isomorphism after precomposition with pushforward along every morphism from
an affine scheme. -/
theorem exists_fourierMukaiKernel_natTrans :
    ∃ (K : Scheme.QCoh (Limits.pullback x y))
      (t : F ⟶ fourierMukai x y K),
      ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsAffine X'],
        IsIso (Functor.whiskerLeft (Scheme.QCoh.pushforward f) t) :=
  sorry

end AlgebraicGeometry.Scheme.QCoh
