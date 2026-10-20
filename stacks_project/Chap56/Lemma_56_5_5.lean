module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.Representability

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Lemma 56.5.5: an admissible functor from a quasi-compact scheme with affine
diagonal admits a Fourier–Mukai kernel and a comparison transformation that
is an isomorphism after precomposition with pushforward from any affine scheme. -/
@[stacks 0GPA] #check
  (AlgebraicGeometry.Scheme.QCoh.exists_fourierMukaiKernel_natTrans :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of R))
      (y : Y ⟶ Spec (CommRingCat.of R))
      [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
      (F : Scheme.QCoh X ⥤ Scheme.QCoh Y) [Scheme.QCoh.Admissible x y F],
      ∃ (K : Scheme.QCoh (Limits.pullback x y))
        (t : F ⟶ Scheme.QCoh.fourierMukai x y K),
        ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsAffine X'],
          IsIso (Functor.whiskerLeft (Scheme.QCoh.pushforward f) t))
