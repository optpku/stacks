/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent.Fpqc
import StacksCheckRecall

universe u v

/- Proposition 35.5.2 (1): every quasi-coherent descent datum for an fpqc covering
family is effective. -/
@[stacks 023T] #check
  (AlgebraicGeometry.Scheme.QCoh.DescentData.isEffective_of_fpqcCovering :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      {family : ι → CategoryTheory.Over S},
      CategoryTheory.Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        AlgebraicGeometry.Scheme.fpqcPrecoverage.coverings S →
        ∀ D : AlgebraicGeometry.Scheme.QCoh.DescentData
            (fun i ↦ (family i).left) (fun i ↦ (family i).hom),
          AlgebraicGeometry.Scheme.QCoh.DescentData.IsEffective D)

/- Proposition 35.5.2 (2): the canonical functor from quasi-coherent modules to descent
data for an fpqc covering family is fully faithful. -/
@[stacks 023T] #check
  (AlgebraicGeometry.Scheme.QCoh.canonicalFunctor.fullyFaithful_of_fpqcCovering :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
      {family : ι → CategoryTheory.Over S},
      CategoryTheory.Presieve.ofArrows (fun i ↦ (family i).left) (fun i ↦ (family i).hom) ∈
        AlgebraicGeometry.Scheme.fpqcPrecoverage.coverings S →
        Nonempty
          (AlgebraicGeometry.Scheme.QCoh.canonicalFunctor
            (fun i ↦ (family i).left) (fun i ↦ (family i).hom)).FullyFaithful)
