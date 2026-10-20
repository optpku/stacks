/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.DeRham.PuncturedLineBundle.Exact
import StacksCheckRecall

@[expose] public section

open CategoryTheory ComplexShape
open AlgebraicGeometry
open RingedSpace.DeRham.PuncturedLineBundle

noncomputable section

universe u

/- Lemma 50.10.2: for an invertible module `ℒ` on `X` and an explicit geometric
presentation of the weight-zero de Rham complex of the punctured line bundle, the sequence
`0 ⟶ Ωᐧ_[X/S] ⟶ Ωᐧ_[L⋆/S, 0] ⟶ Ωᐧ_[X/S]⟦-1⟧ ⟶ 0` is short exact. -/
@[stacks 0FUF] #check (puncturedLineBundleSequence_shortExact :
  ∀ {S X : Scheme.{u}} (f : X ⟶ S) (ℒ : X.Modules)
    [Scheme.Modules.Invertible ℒ]
    (P : Scheme.RelativeSpectrumOver (Scheme.SymmetricAlgebra.qcAlgebra ℒ))
    [Scheme.IsRelativeSpectrumOver P]
    (D : WeightZeroDeRham f ℒ P),
      (sequence f ℒ P D).ShortExact)
