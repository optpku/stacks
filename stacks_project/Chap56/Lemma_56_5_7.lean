/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.Exact
public import stacks_project.Chap56.Lemma_56_5_2
public import stacks_project.Chap56.Lemma_56_5_7_ExactAdmissible
public import stacks_project.Chap56.Lemma_56_5_7_Kernel

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

/- Lemma 56.5.7: for a quasi-compact scheme with affine diagonal, the concrete
Fourier--Mukai assignment is an equivalence between kernels flat over the source
with vanishing positive higher direct images for every quasicoherent input, and
exact relatively R-linear functors commuting with arbitrary direct sums. -/
@[stacks 0FZH] #check
  (AlgebraicGeometry.Scheme.QCoh.exactFourierMukai_isEquivalence :
    ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of R))
      (y : Y ⟶ Spec (CommRingCat.of R))
      [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
      [HasInjectiveResolutions (Limits.pullback x y).Modules],
      (AlgebraicGeometry.Scheme.QCoh.exactFourierMukai x y).IsEquivalence)
