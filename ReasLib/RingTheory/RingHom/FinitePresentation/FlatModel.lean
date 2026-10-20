/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.RingHom.FlatModel
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Flat Models of Finitely Presented Modules

This leaf owns the absolute finite-type-over-`ℤ` model theorem for a finitely
presented ring map and a finitely presented module that is flat after
restriction of scalars.  The reusable model data lives in
`RingHom.FlatModel`.
-/

universe uR uS uR0 uStageS uM uStageM

namespace RingHom.FlatModel

set_option linter.checkUnivs false in
/-- Lemma 10.168.1 (1), tag `02JO`: a finitely presented module that is flat
over the source of a finitely presented map admits a model over a finite-type
`ℤ`-algebra.  The stage map is finite type, the stage module is finite, and
the comparison square is returned as a reusable `RingHom.FlatModel`. -/
@[stacks 02JO "flat finite-type module model over a finite-type integer algebra"]
theorem exists_overInt
    {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]
    (f : R →+* S) {M : Type uM} [AddCommGroup M] [Module S M]
    [Module.FinitePresentation S M] (hf : f.FinitePresentation)
    (hflat : Module.FlatAlong f M) :
    ∃ (R₀ : Type uR0) (_ : CommRing R₀) (r : R₀ →+* R)
      (S₀ : Type uStageS) (_ : CommRing S₀) (stageMap : R₀ →+* S₀)
      (M₀ : Type uStageM) (_ : AddCommGroup M₀) (_ : Module S₀ M₀)
      (targetMap : S₀ →+* S),
      ∃ P : RingHom.FlatModel (M := M) (M₀ := M₀) f r stageMap targetMap,
        P.finiteType := sorry

end RingHom.FlatModel
