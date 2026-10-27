/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Model
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite homogeneous-localization models

@stack 052N

This leaf supplies the existence theorem for the concrete graded algebra and
module model owned by `HomogeneousLocalization.Model`.
-/

universe u u' v

namespace HomogeneousLocalization.Model

/-- Lemma 10.57.10 (052N): a finite module over a finite-type algebra admits
an `N`-graded homogeneous-localization model generated in degree one and
carrying the full finite specification. -/
@[stacks 052N]
theorem exists_of_finiteModule
    {R : Type u} {R' : Type u'} {M : Type v}
    [CommRing R] [CommRing R'] [Algebra R R']
    [AddCommGroup M] [Module R' M]
    [Algebra.FiniteType R R'] [Module.Finite R' M] :
    ∃ model : HomogeneousLocalization.Model.{u, u', v, max u (max u' v), 0,
        max u (max u' v)} (R := R) (R' := R') (M := M)
      (ι := ℕ) (d := 1),
      model.Spec := sorry

end HomogeneousLocalization.Model
