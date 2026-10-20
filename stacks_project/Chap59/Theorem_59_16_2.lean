/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Fpqc
import StacksCheckRecall

universe u v

/- Theorem 59.16.2: If an indexed family of scheme morphisms is an fpqc covering,
then every quasi-coherent descent datum for that family is effective. -/
@[stacks 03O8] #check
  (AlgebraicGeometry.Scheme.QCoh.DescentData.isEffective_of_fpqcCovering :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      {family : ι → CategoryTheory.Over S},
      CategoryTheory.Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        AlgebraicGeometry.Scheme.fpqcPrecoverage.coverings S →
        ∀ D : AlgebraicGeometry.Scheme.QCoh.DescentData
            (fun i ↦ (family i).left) (fun i ↦ (family i).hom),
          AlgebraicGeometry.Scheme.QCoh.DescentData.IsEffective D)
