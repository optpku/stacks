module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.Affine
public import stacks_project.Chap56.«56_5_1_1»
public import stacks_project.Chap56.Example_56_5_1
public import stacks_project.Chap56.Lemma_56_5_2_Admissible

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

/- Lemma 56.5.2: if `X` is affine, the kernel-to-Fourier--Mukai assignment is
an equivalence between quasicoherent kernels and admissible functors. -/
@[stacks 0FZD] #check
  (AlgebraicGeometry.Scheme.QCoh.fourierMukai_isEquivalence :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}},
      (x : X ⟶ Spec (CommRingCat.of R)) →
      (y : Y ⟶ Spec (CommRingCat.of R)) →
      [IsAffine X] →
      (AlgebraicGeometry.Scheme.QCoh.admissibleFourierMukai x y).IsEquivalence)
