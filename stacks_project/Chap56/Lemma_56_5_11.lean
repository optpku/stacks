/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.Generation
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/- Lemma 56.5.11: in the correspondence of Lemma 56.5.7, if `F` is the
Fourier--Mukai functor associated to an exact kernel `K` and `X` is separated
and flat over `R`, then there is a surjection
`boxProduct x y (structureSheaf X) ((fourierMukai x y K).obj (structureSheaf X)) ⟶ K`. -/
@[stacks 0FZJ] #check (AlgebraicGeometry.Scheme.QCoh.exists_epi_boxProduct_fourierMukai :
  ∀ {R : Type u} [CommRing R] {X Y : Scheme.{u}}
    (x : X ⟶ Spec (CommRingCat.of R)) (y : Y ⟶ Spec (CommRingCat.of R))
    [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
    [HasInjectiveResolutions (Limits.pullback x y).Modules]
    [IsSeparated x] [Flat x]
    (K : Scheme.QCoh (Limits.pullback x y)) [IsExactFourierMukaiKernel x y K],
    ∃ φ : boxProduct x y (structureSheaf X)
        ((fourierMukai x y K).obj (structureSheaf X)) ⟶ K,
      Epi φ)

end AlgebraicGeometry.Scheme.QCoh
