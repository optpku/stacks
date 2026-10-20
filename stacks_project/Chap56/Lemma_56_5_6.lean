module

import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Lemma 56.5.6 -/
@[stacks 0FZG] #check
  (AlgebraicGeometry.Scheme.QCoh.fourierMukaiKernel_flatOver_of_exact :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of R))
      (y : Y ⟶ Spec (CommRingCat.of R))
      [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
      (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) [AlgebraicGeometry.Scheme.QCoh.Admissible x y F]
      (hF : exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) F)
      (K : Scheme.QCoh (Limits.pullback x y))
      (t : F ⟶ AlgebraicGeometry.Scheme.QCoh.fourierMukai x y K)
      (hlocal : ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsAffine X'],
        IsIso (Functor.whiskerLeft (Scheme.QCoh.pushforward f) t)),
      Scheme.Modules.flatOver K.obj (Limits.pullback.fst x y))

#check
  (AlgebraicGeometry.Scheme.QCoh.fourierMukai_flatOver_of_exact :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of R))
      (y : Y ⟶ Spec (CommRingCat.of R)) [IsAffine X]
      (K : Scheme.QCoh (Limits.pullback x y))
      (hF : exactFunctor (Scheme.QCoh X) (Scheme.QCoh Y) (AlgebraicGeometry.Scheme.QCoh.fourierMukai x y K)),
      Scheme.Modules.flatOver K.obj (Limits.pullback.fst x y))
