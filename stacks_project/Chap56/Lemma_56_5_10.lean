/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FourierMukai.UniversalVanishing

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

universe u

/- Lemma 56.5.10: if `K` is an exact Fourier--Mukai kernel on `X ×_R Y` as in
Lemma 56.5.7 (2), then for every scheme `T` over `R`, every quasicoherent
`F` on `T ×_R X`, and every `q > 0`, the higher direct image
`R^q pr₁₃,*(pr₁₂^* F ⊗ pr₂₃^* K)` on `T ×_R Y` vanishes. -/
@[stacks 0FZI] #check
  (AlgebraicGeometry.Scheme.QCoh.higherDirectImage_tripleTensor_isZero :
    ∀ {R : Type u} [CommRing R] {X Y T : Scheme.{u}}
      (x : X ⟶ Spec (CommRingCat.of R))
      (y : Y ⟶ Spec (CommRingCat.of R))
      (t : T ⟶ Spec (CommRingCat.of R))
      [HasInjectiveResolutions (Limits.pullback x y).Modules]
      [HasInjectiveResolutions (Scheme.QCoh.triplePullback x y t).Modules]
      [CompactSpace X] [IsAffineHom (prod.lift (𝟙 X) (𝟙 X))]
      (K : Scheme.QCoh (Limits.pullback x y)) [Scheme.QCoh.IsExactFourierMukaiKernel x y K]
      (F : Scheme.QCoh (Limits.pullback t x)) (q : ℕ), 0 < q →
      IsZero (Scheme.QCoh.higherDirectImage_tripleTensor x y t K F q))
