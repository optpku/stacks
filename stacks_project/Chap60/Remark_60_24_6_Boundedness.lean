/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Crystalline.HigherDirectImage
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Crystalline
open SheafOfModules

universe u

/- Remark 60.24.6 (Boundedness): in the situation of Remark 60.24.1, assume
that `S ⟶ S'` is quasi-compact and quasi-separated and that `X ⟶ S₀` is of
finite type and quasi-separated. Then there exists an integer `i₀` such that
for any crystal `F` in quasi-coherent `𝒪_{X/S}`-modules we have
`R^i f_cris,* F = 0` for all `i > i₀`. -/
@[stacks 07MQ] #check (crystallineHigherDirectImage_eventually_isZero :
  ∀ {p : ℕ} [Fact p.Prime] (B B' : Base.{u} p)
    (g : DividedPowerScheme.Hom B.dividedPowerScheme B'.dividedPowerScheme)
    (hbase : g.base ≫ B'.toSpec = B.toSpec)
    (f : B.source ⟶ B'.source)
    (hf : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
    [QuasiCompact g.base] [QuasiSeparated g.base]
    [AlgebraicGeometry.Scheme.Hom.FiniteType B.sourceToClosed]
    [QuasiSeparated B.sourceToClosed],
    ∃ i₀ : ℕ, ∀ (F : RingedSite.ModuleCat.{u + 1} B.ringedSite)
      [IsCrystalInQuasiCoherentModules F] (i : ℕ),
      i₀ < i → CategoryTheory.Limits.IsZero
        (RingedSite.ToposHom.higherDirectImageModule.{u + 1, u, u + 1, u, u + 1}
          (Ringed.morphism B B' g hbase f hf) F i))
