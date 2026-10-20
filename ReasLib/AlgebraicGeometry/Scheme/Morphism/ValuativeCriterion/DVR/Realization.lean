/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR.GenericPoint
public import ReasLib.AlgebraicGeometry.Scheme.Topology.DiscreteValuation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# DVR-valuative squares from specialization realizations

This leaf is the one-way bridge from the topology realization owner to the
Morphism-valuative-criterion owners.  The topology leaves do not depend on
this file; callers that already have a `DvrRealization` can use the canonical
criterion payload without rebuilding a square by hand.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace _root_.Specializes.DvrRealization

/-- Turn a discrete valuation realization into the corresponding Mathlib DVR-valuative square. -/
@[stacks 054F "DVR realization as a DVR-valuative square"]
noncomputable def toDvrValuativeCommSq
    {X Y : Scheme.{u}} {x' x : X} (D : DvrRealization x' x) (f : X ⟶ Y) :
    AlgebraicGeometry.DvrValuativeCommSq f :=
  ⟨D.toValuativeCommSq f, D.dvr⟩

namespace WithFieldMap

/-- Adapt an identity-residue-map realization in `X` to the pointwise DVR square over `f`.

The identity index makes the generic map the canonical residue-field map of `x'`; the
commutative-square field is proposition-valued and is left as the proof obligation of this
statement-stage owner.
-/
@[stacks 0CM2 "DVR realization adapter for a residue-field valuative square"]
noncomputable def toDvrValuativeCommSqAt
    {X S : Scheme.{u}} (f : X ⟶ S) {points : Set X} {x' x : X}
    (hx' : x' ∈ points)
    (D : WithFieldMap (K := (X.residueField x' : Type u)) x' x
      (𝟙 (X.residueField x'))) :
    AlgebraicGeometry.DvrValuativeCommSqAt f points where
  sourcePoint := x'
  sourcePoint_mem := hx'
  R := D.V
  commRing := ValuationSubring.instCommRingSubtypeMem D.V
  domain := ValuationSubring.instIsDomainSubtypeMem D.V
  dvr := D.dvr
  algebra := ValuationSubring.instAlgebraSubtypeMem D.V
  isFractionRing := ValuationSubring.instIsFractionRingSubtypeMem D.V
  toTarget := D.hom ≫ f
  commSq := sorry

end WithFieldMap

end _root_.Specializes.DvrRealization
