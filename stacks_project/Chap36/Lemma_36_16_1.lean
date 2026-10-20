/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Ample

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.16.1: a nonzero object of `D_QCoh(𝒪_X)` has nonzero derived global
cohomology in some degree after tensoring with a nonnegative tensor power of an
ample invertible module. -/
@[stacks 0BQR] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.exists_nonzero_twistedCohomology :
    ∀ {X : Scheme.{u}} (L : X.Modules)
      [Scheme.Modules.Invertible L] [Scheme.Modules.IsAmple L]
      (K : Scheme.ModuleDerived.Quasicoherent X) (hK : ¬ IsZero K),
      ∃ (n : ℕ) (p : ℤ),
        ¬ IsZero ((RingedSpace.moduleDerivedCohomologyFunctor X.toRingedSpace p).obj
          (K.obj ⊗ᴸ (DerivedCategory.singleFunctor X.Modules 0).obj
            (RingedSpace.TensorPower.sheaf L n))))

end AlgebraicGeometry.Scheme.DerivedQCoh
