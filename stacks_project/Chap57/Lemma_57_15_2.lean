/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FourierMukai.Equivalence

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Lemma 57.15.2 (1): if `K` is the Fourier--Mukai kernel of a relative
equivalence from `X` to `Y` over `S`, then the corresponding Fourier--Mukai
functor `Φ_K : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of Lemma 57.8.2 is an equivalence. -/
@[stacks 0G0J]
#check (FourierMukaiObject.quasicoherentFunctor_isEquivalence :
  ∀ {S : Scheme.{u}} {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    [IsIso (C := FourierMukaiObject S) (Quotient.mk'' K : X ⟶ Y)],
    (Scheme.FourierMukai.quasicoherent X.hom Y.hom
      ((Scheme.PerfectDerived.toDerivedQCoh
        (Limits.pullback X.hom Y.hom)).obj K)).IsEquivalence)

/- Lemma 57.15.2 (2): if `K` is the Fourier--Mukai kernel of a relative
equivalence from `X` to `Y` over `S`, then the corresponding Fourier--Mukai
functor `Φ_K : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` of Lemma 57.8.4 is an equivalence. -/
@[stacks 0G0J]
#check (FourierMukaiObject.perfectFunctor_isEquivalence :
  ∀ {S : Scheme.{u}} {X Y : FourierMukaiObject S}
    (K : @RingedSpace.ModuleDerived.Perfect
      (Limits.pullback X.hom Y.hom).toRingedSpace)
    [IsIso (C := FourierMukaiObject S) (Quotient.mk'' K : X ⟶ Y)],
    (Scheme.FourierMukai.perfect X.hom Y.hom K).IsEquivalence)
