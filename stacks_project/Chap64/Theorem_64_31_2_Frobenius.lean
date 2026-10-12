/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Finiteness.Cardinality
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import stacks_project.Chap58.Lemma_58_6_3_GaloisFiber
public import stacks_project.Chap58.Lemma_58_14_3_Induced
public import stacks_project.Chap58.Theorem_58_6_2
public import stacks_project.Chap64.Definition_64_19_1_FrobeniusStalk

/-!
# Geometric Frobenius in the étale fundamental group

This leaf owns the residue cardinality `q_v = #κ(v)` at a closed point and the
geometric Frobenius element `F_v` in the local étale fundamental group, together
with its transport to a fixed base point along a fibre isomorphism.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale
open CategoryTheory FiniteField TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]
variable (X : SchemeOverField k)

/-- The residue field at a closed point of a finite-type scheme over a finite
field is finite. -/
instance instFinite_closedPointResidueField [Finite k]
    [LocallyOfFiniteType X.hom] (v : closedPoints X.left) :
    Finite (X.left.residueField v.1) :=
  Module.finite_of_finite k

/-- The residue field at a closed point of a finite-type scheme over a finite
field admits a `Fintype` instance. -/
noncomputable instance instFintype_closedPointResidueField [Finite k]
    [LocallyOfFiniteType X.hom] (v : closedPoints X.left) :
    Fintype (X.left.residueField v.1) :=
  Fintype.ofFinite _

/-- The residue cardinality `q_v = #κ(v)` of a closed point of a finite-type
scheme over a finite field. -/
def residueCard [Finite k] [LocallyOfFiniteType X.hom] (v : closedPoints X.left) :
    ℕ :=
  Nat.card (X.left.residueField v.1)

/-- `residueCard` is the cardinality of the residue field at the closed point. -/
theorem residueCard_spec [Finite k] [LocallyOfFiniteType X.hom]
    (v : closedPoints X.left) :
    residueCard X v = Nat.card (X.left.residueField v.1) := sorry

/-- The residue cardinality equals `#k` raised to the residue degree over `k`. -/
theorem residueCard_pow_residueDegree [Finite k] [LocallyOfFiniteType X.hom]
    (v : closedPoints X.left) :
    residueCard X v = Nat.card k ^ X.hom.residueDegree v.1 := sorry

/-- Unfolding of `geometricPointOverClosedPoint` as postcomposition of the
residue-field geometric point along `fromSpecResidueField`. -/
theorem geometricPointOverClosedPoint_spec (v : closedPoints X.left) :
    geometricPointOverClosedPoint X v =
      geometricPointPostcomp
        (specFieldGeometricPoint (X.left.residueField v.1)
          (AlgebraicClosure (X.left.residueField v.1)))
        (X.left.fromSpecResidueField v.1) := rfl

/-- Geometric Frobenius of the residue field, as an element of the étale
fundamental group of `X` at the canonical geometric point over `v`. It is the
image of the inverse of arithmetic Frobenius under
`galoisToFundamentalGroup` and `etaleFundamentalGroupMap` along
`fromSpecResidueField`. -/
def localGeometricFrobenius [Finite k] [ConnectedSpace X.left]
    [LocallyOfFiniteType X.hom] (v : closedPoints X.left) :
    Aut (standardFiniteEtaleFiber (geometricPointOverClosedPoint X v)) :=
  etaleFundamentalGroupMap (X.left.fromSpecResidueField v.1)
    (specFieldGeometricPoint (X.left.residueField v.1)
      (AlgebraicClosure (X.left.residueField v.1)))
    (galoisToFundamentalGroup (X.left.residueField v.1)
      (AlgebraicClosure (X.left.residueField v.1))
      (AlgebraicClosure (X.left.residueField v.1))
      (frobeniusAlgEquivOfAlgebraic (X.left.residueField v.1)
        (AlgebraicClosure (X.left.residueField v.1)))⁻¹)

/-- `localGeometricFrobenius` is the image of residue-field geometric Frobenius
in the local étale fundamental group at the canonical geometric point over `v`. -/
theorem localGeometricFrobenius_spec [Finite k] [ConnectedSpace X.left]
    [LocallyOfFiniteType X.hom] (v : closedPoints X.left) :
    localGeometricFrobenius X v =
      etaleFundamentalGroupMap (X.left.fromSpecResidueField v.1)
        (specFieldGeometricPoint (X.left.residueField v.1)
          (AlgebraicClosure (X.left.residueField v.1)))
        (galoisToFundamentalGroup (X.left.residueField v.1)
          (AlgebraicClosure (X.left.residueField v.1))
          (AlgebraicClosure (X.left.residueField v.1))
          (frobeniusAlgEquivOfAlgebraic (X.left.residueField v.1)
            (AlgebraicClosure (X.left.residueField v.1)))⁻¹) := sorry

/-- Geometric Frobenius `F_v` in `π₁(X, xbar)`, obtained by transporting
`localGeometricFrobenius` along an explicit isomorphism of finite étale fibre
functors. Named `etaleGeometricFrobenius` to avoid colliding with the scheme
endomorphism `geometricFrobenius`. -/
def etaleGeometricFrobenius [Finite k] [ConnectedSpace X.left]
    [LocallyOfFiniteType X.hom] (xbar : GeometricPoint X.left)
    (v : closedPoints X.left)
    (ι : standardFiniteEtaleFiber (geometricPointOverClosedPoint X v) ≅
      standardFiniteEtaleFiber xbar) :
    Aut (standardFiniteEtaleFiber xbar) :=
  autIso_of_geometricPoints ι (localGeometricFrobenius X v)

/-- Unfolding of `etaleGeometricFrobenius` as transport of local geometric
Frobenius along the given fibre isomorphism. -/
theorem etaleGeometricFrobenius_spec [Finite k] [ConnectedSpace X.left]
    [LocallyOfFiniteType X.hom] (xbar : GeometricPoint X.left)
    (v : closedPoints X.left)
    (ι : standardFiniteEtaleFiber (geometricPointOverClosedPoint X v) ≅
      standardFiniteEtaleFiber xbar) :
    etaleGeometricFrobenius X xbar v ι =
      autIso_of_geometricPoints ι (localGeometricFrobenius X v) := sorry

end AlgebraicGeometry.SchemeOverField
