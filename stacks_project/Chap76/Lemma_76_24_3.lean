/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.IdealPowers
import StacksCheckRecall

/-!
# Infinitesimal flatness over a Noetherian affine base

If an algebraic space is locally of finite presentation over the spectrum of a
Noetherian ring and a coherent module is relatively flat on every infinitesimal
neighbourhood of `V(I)`, then the relative-flat locus contains the preimage of
`V(I)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace.Modules
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization (toBase)

universe u

/- Lemma 76.24.3: Let `A` be a Noetherian ring and `I ⊆ A` an ideal. Let `X` be an
algebraic space locally of finite presentation over `S = Spec A`. For `n ≥ 1` set
`S_n = Spec(A ⧸ I ^ n)` and `X_n = S_n ×_S X`. Let `F` be a coherent `𝒪_X`-module.
If for every `n ≥ 1` the pullback `F_n` of `F` to `X_n` is flat over `S_n`, then the
open locus where `F` is flat over `S` contains the inverse image of `V(I)` under
`X ⟶ S`.

The official statement writes “pullback to `X`” and “flat over `X`”; the proof and
Algebra 10.99.11 show the intended maps are the pullback of `F` to `X_n` and the
open locus of flatness over `S`. -/
@[stacks 08VP] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.zeroLocus_preimage_subset_flatOverLocus :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
      (X : AlgebraicSpace (Spec (CommRingCat.of A)))
      [LocallyOfFinitePresentation (toBase X)] (F : X.Modules) [F.IsCoherent]
      (hflat : ∀ n, 1 ≤ n →
        flatOver (pullbackIdealPower I F n)
          (Limits.pullback.fst (idealPowerι I n) (toBase X))),
      Points.base ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ⊆
        flatOverLocus F (toBase X))
