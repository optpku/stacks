module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Pullbacks
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Diagonal
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.Affine
public import stacks_project.Chap56.«56_5_1_1»
public import stacks_project.Chap56.Lemma_56_5_2_Admissible
public import stacks_project.Chap56.Lemma_56_5_5_Reconstruction

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

/-- Lemma 56.5.5: if `X` is quasi-compact with affine diagonal, then every
admissible functor `F : Scheme.QCoh X ⥤ Scheme.QCoh Y` admits a quasi-coherent
kernel `K` on `Limits.pullback x y` and a natural transformation
`t : F ⟶ fourierMukai x y K` (the Fourier--Mukai functor of 56.5.1.1) such that
whiskering `t` by `Scheme.QCoh.pushforward f` is an isomorphism for every
morphism `f : X' ⟶ X` with affine source. Affine diagonal makes such morphisms
affine by Morphisms, Lemma 29.11.12. -/
@[stacks 0GPA]
theorem exists_fourierMukaiKernel_natTrans :
    ∃ (K : Scheme.QCoh (Limits.pullback x y))
      (t : F ⟶ fourierMukai x y K),
      ∀ {X' : Scheme.{u}} (f : X' ⟶ X) [IsAffine X'],
        IsIso (Functor.whiskerLeft (Scheme.QCoh.pushforward f) t) :=
  sorry

end AlgebraicGeometry.Scheme.QCoh
