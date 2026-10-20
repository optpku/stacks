/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import stacks_project.Chap57.Lemma_57_8_2_FourierMukai
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.FourierMukai

/- Lemma 57.8.2: the Fourier--Mukai transform preserves quasicoherent cohomology when the
first structural morphism is quasi-compact and quasi-separated and the kernel is quasicoherent. -/
@[stacks 0FYR] #check
  (AlgebraicGeometry.Scheme.FourierMukai.mapsTo :
    ∀ {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
      [QuasiCompact f] [QuasiSeparated f]
      (K : RingedSpace.ModuleDerived (Limits.pullback f g).toRingedSpace)
      (hK : Scheme.ModuleDerived.quasicoherentProperty (Limits.pullback f g) K),
      Scheme.ModuleDerived.quasicoherentProperty X ≤
        (Scheme.ModuleDerived.quasicoherentProperty Y).inverseImage
          (AlgebraicGeometry.Scheme.FourierMukai.functor f g K))

end AlgebraicGeometry.Scheme.FourierMukai
