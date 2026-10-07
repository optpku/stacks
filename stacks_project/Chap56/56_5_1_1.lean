module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

@[expose] public section

noncomputable section

universe u

/-- Compatibility spelling for the affine-base Fourier--Mukai functor. -/
noncomputable def fourierMukaiFunctor
    {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of R))
    (y : Y ⟶ Spec (CommRingCat.of R))
    [CompactSpace X] [QuasiSeparatedSpace X]
    (K : Scheme.QCoh (Limits.pullback x y)) :
    Scheme.QCoh X ⥤ Scheme.QCoh Y :=
  AlgebraicGeometry.Scheme.QCoh.fourierMukaiFunctor x y K

/- 56.5.1.1: For a commutative ring `R`, schemes `X` and `Y` over
`Spec (CommRingCat.of R)`, and qcqs `X`, with kernel `K` on `Limits.pullback x y`,
the Fourier--Mukai functor is the composition of
`Scheme.QCoh.pullback (Limits.pullback.fst x y)`, tensoring by `K`, and
`Scheme.QCoh.pushforward (Limits.pullback.snd x y)`. -/
@[stacks 0FZC]
#check (AlgebraicGeometry.Scheme.QCoh.fourierMukaiFunctor :
  ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
    (x : X ⟶ Spec (CommRingCat.of R)) →
    (y : Y ⟶ Spec (CommRingCat.of R)) →
    [CompactSpace X] → [QuasiSeparatedSpace X] →
    Scheme.QCoh (Limits.pullback x y) →
    Scheme.QCoh X ⥤ Scheme.QCoh Y)
