/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.OpenImmersion.Pullback
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

/- Lemma 32.5.2: in a cartesian square `B → R ← R'` with pullback ring `B'`, if an open
`W' ⊆ Spec(R')` is a finite union of basic opens `D(f_i)` such that `t(f_i) = s(g_i)` for
`g_i ∈ B` and the canonical map `B[1/g_i] → R[1/s(g_i)]` is bijective, then the induced
morphism `W' ⟶ Spec(B')` is an open immersion. -/
@[stacks 01Z9] #check
  (CategoryTheory.IsPullback.isOpenImmersion_restrictSpecMap_of_basicOpenCover :
    ∀ {B R R' B' : Type u} [CommRing B] [CommRing R] [CommRing R'] [CommRing B']
      (s : B →+* R) (t : R' →+* R) (left : B' →+* B) (right : B' →+* R')
      (hcart : IsPullback (ofHom left) (ofHom right) (ofHom s) (ofHom t))
      {n : ℕ} (W' : (Spec (of R')).Opens) (f : Fin n → R') (g : Fin n → B)
      (hW' : W' = ⨆ i, PrimeSpectrum.basicOpen (f i))
      (hfg : ∀ i, t (f i) = s (g i))
      (hlocal : ∀ i, Function.Bijective (Localization.awayMap s (g i))),
      IsOpenImmersion (W'.ι ≫ Spec.map (ofHom right)))
