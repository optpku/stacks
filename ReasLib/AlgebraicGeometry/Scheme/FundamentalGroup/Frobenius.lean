/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Finiteness.Cardinality
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Etale.ClosedPointFrobenius
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Galois
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FundamentalGroup
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Map

@[expose] public section
noncomputable section
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory FiniteField TopologicalSpace
universe u
namespace AlgebraicGeometry.SchemeOverField
variable {k : Type u} [Field k]
variable (X : SchemeOverField k)

/-- The cardinality of the residue field at a closed point. -/
def residueCard [Finite k] [LocallyOfFiniteType X.hom] (v : closedPoints X.left) : ℕ :=
  Nat.card (X.left.residueField v.1)

/-- The residue cardinality unfolds to the cardinality of the residue field. -/
theorem residueCard_spec [Finite k] [LocallyOfFiniteType X.hom] (v : closedPoints X.left) :
    residueCard X v = Nat.card (X.left.residueField v.1) := rfl

/-- The residue cardinality is the base cardinality to the residue degree. -/
theorem residueCard_pow_residueDegree [Finite k] [LocallyOfFiniteType X.hom]
    (v : closedPoints X.left) :
    residueCard X v = Nat.card k ^ X.hom.residueDegree v.1 := sorry

/-- The canonical geometric point over a closed point is the residue-field point postcomposed
with the structural morphism. -/
theorem geometricPointOverClosedPoint_spec (v : closedPoints X.left) :
    geometricPointOverClosedPoint X v =
      GeometricPoint.map
        (specFieldGeometricPoint (X.left.residueField v.1)
          (AlgebraicClosure (X.left.residueField v.1)))
        (X.left.fromSpecResidueField v.1) := rfl

/-- The image in the local fundamental group of inverse arithmetic Frobenius. -/
def localGeometricFrobenius [Finite k] [ConnectedSpace X.left]
    [LocallyOfFiniteType X.hom] (v : closedPoints X.left) :
    Aut (GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v)) :=
  GeometricPoint.fundamentalGroupMap (X.left.fromSpecResidueField v.1)
    (specFieldGeometricPoint (X.left.residueField v.1)
      (AlgebraicClosure (X.left.residueField v.1)))
    (galoisToFundamentalGroup (X.left.residueField v.1)
      (AlgebraicClosure (X.left.residueField v.1))
      (AlgebraicClosure (X.left.residueField v.1))
      (frobeniusAlgEquivOfAlgebraic (X.left.residueField v.1)
        (AlgebraicClosure (X.left.residueField v.1))))⁻¹

/-- The defining formula for local geometric Frobenius. -/
theorem localGeometricFrobenius_spec [Finite k] [ConnectedSpace X.left]
    [LocallyOfFiniteType X.hom] (v : closedPoints X.left) :
    localGeometricFrobenius X v =
      GeometricPoint.fundamentalGroupMap (X.left.fromSpecResidueField v.1)
        (specFieldGeometricPoint (X.left.residueField v.1)
          (AlgebraicClosure (X.left.residueField v.1)))
        (galoisToFundamentalGroup (X.left.residueField v.1)
          (AlgebraicClosure (X.left.residueField v.1))
          (AlgebraicClosure (X.left.residueField v.1))
          (frobeniusAlgEquivOfAlgebraic (X.left.residueField v.1)
            (AlgebraicClosure (X.left.residueField v.1))))⁻¹ := rfl

/-- Geometric Frobenius transported to a chosen geometric base point. -/
def etaleGeometricFrobenius [Finite k] [ConnectedSpace X.left]
    [LocallyOfFiniteType X.hom] (xbar : GeometricPoint X.left)
    (v : closedPoints X.left)
    (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
      GeometricPoint.finiteFiber xbar) : Aut (GeometricPoint.finiteFiber xbar) :=
  GeometricPoint.autEquiv ι (localGeometricFrobenius X v)

/-- The defining transport formula for geometric Frobenius at a base point. -/
theorem etaleGeometricFrobenius_spec [Finite k] [ConnectedSpace X.left]
    [LocallyOfFiniteType X.hom] (xbar : GeometricPoint X.left)
    (v : closedPoints X.left)
    (ι : GeometricPoint.finiteFiber (geometricPointOverClosedPoint X v) ≅
      GeometricPoint.finiteFiber xbar) :
    etaleGeometricFrobenius X xbar v ι =
      GeometricPoint.autEquiv ι (localGeometricFrobenius X v) := rfl

end AlgebraicGeometry.SchemeOverField
