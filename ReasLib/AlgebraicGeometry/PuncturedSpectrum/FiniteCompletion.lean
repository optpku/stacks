/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.Completion
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite morphisms and punctured-spectrum completion

Finite morphisms over the punctured spectrum of a Noetherian local ring descend
from the maximal-ideal completion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A finite morphism over a punctured spectrum and a compatible finite morphism over
the completed spectrum descend to a finite morphism over the original spectrum. -/
theorem exists_finite_morphism_of_completion
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {V Y' : Scheme.{u}}
    (v : V ⟶ PuncturedSpectrum.scheme A) [IsFinite v]
    (y' : Y' ⟶
      Spec (CommRingCat.of (AdicCompletion (IsLocalRing.maximalIdeal A) A)))
      [IsFinite y']
    (h : Nonempty
      (Over.mk (pullback.snd v (PuncturedSpectrum.completionMap A)) ≅
        Over.mk
          (pullback.snd y'
            (PuncturedSpectrum.puncturedOpen
              (AdicCompletion (IsLocalRing.maximalIdeal A) A)).ι))) :
    ∃ (Y : Scheme.{u}) (y : Y ⟶ Spec (CommRingCat.of A)),
      IsFinite y ∧
        Nonempty
          (Over.mk v ≅
            Over.mk (pullback.snd y (PuncturedSpectrum.puncturedOpen A).ι)) ∧
        Nonempty
          (Over.mk y' ≅
            Over.mk (pullback.snd y (PuncturedSpectrum.completionSpecMap A))) := sorry

/-- A finite étale cover of a punctured spectrum extends over the spectrum if and only if
its base change to the maximal-ideal completion extends over the completed spectrum. -/
theorem finiteEtale_punctured_completion_iff
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (V : Scheme.FiniteEtale (PuncturedSpectrum.scheme A)) :
    let X : Scheme := Spec (CommRingCat.of A)
    let U : X.Opens := PuncturedSpectrum.puncturedOpen A
    let Ahat : Type u := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let X' : Scheme := Spec (CommRingCat.of Ahat)
    let U' : X'.Opens := PuncturedSpectrum.puncturedOpen Ahat
    let V' : Scheme.FiniteEtale (PuncturedSpectrum.scheme Ahat) :=
      (Scheme.finiteEtaleBaseChange (PuncturedSpectrum.completionMap A)).obj V
    (∃ Y : Scheme.FiniteEtale X,
        Nonempty ((Scheme.finiteEtaleBaseChange U.ι).obj Y ≅ V)) ↔
      (∃ Y' : Scheme.FiniteEtale X',
        Nonempty ((Scheme.finiteEtaleBaseChange U'.ι).obj Y' ≅ V')) := sorry

end AlgebraicGeometry.Scheme.Hom
