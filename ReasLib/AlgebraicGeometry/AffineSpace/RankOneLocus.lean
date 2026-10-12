/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Variety.AffinePresentation

/-!
# Rank-one matrices as a locally closed subset of affine 9-space

This file records the set `V_0` of `3 × 3` rank-one matrices over a field `k`,
the identification `Mat(3 × 3, k) = k^9` via `finProdFinEquiv`, and the Zariski
locally closed rank-exactly-one locus `V` in `AffineSpaceOverField k 9`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AffineSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AffineSpace

/-- The set of `3 × 3` matrices of rank exactly `1` over `k`. -/
def rankOneMatrices (k : Type u) [Field k] : Set (Matrix (Fin 3) (Fin 3) k) :=
  {A | A.rank = 1}

/-- Membership in `rankOneMatrices` is the condition `Matrix.rank A = 1`. -/
theorem mem_rankOneMatrices_iff (k : Type u) [Field k] (A : Matrix (Fin 3) (Fin 3) k) :
    A ∈ rankOneMatrices k ↔ A.rank = 1 := sorry

/-- Flatten a `3 × 3` matrix to a coordinate `9`-tuple along `finProdFinEquiv`. -/
def coordsOfMatrix (k : Type u) [Field k] (A : Matrix (Fin 3) (Fin 3) k) : Fin 9 → k :=
  fun t ↦
    let indices := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm t
    A indices.1 indices.2

/-- Rebuild a `3 × 3` matrix from a coordinate `9`-tuple along `finProdFinEquiv`. -/
def matrixOfCoords (k : Type u) [Field k] (a : Fin 9 → k) : Matrix (Fin 3) (Fin 3) k :=
  .of fun i j ↦ a (finProdFinEquiv (i, j))

/-- `coordsOfMatrix` is a left inverse of `matrixOfCoords`. -/
theorem coordsOfMatrix_matrixOfCoords (k : Type u) [Field k] (a : Fin 9 → k) :
    coordsOfMatrix k (matrixOfCoords k a) = a := sorry

/-- `matrixOfCoords` is a left inverse of `coordsOfMatrix`. -/
theorem matrixOfCoords_coordsOfMatrix (k : Type u) [Field k]
    (A : Matrix (Fin 3) (Fin 3) k) :
    matrixOfCoords k (coordsOfMatrix k A) = A := sorry

/-- The generic `3 × 3` matrix of standard affine coordinates on
`AffineSpaceOverField k 9`, indexed by `finProdFinEquiv`. -/
def genericMatrix (k : Type u) [Field k] :
    Matrix (Fin 3) (Fin 3) Γ(AffineSpaceOverField k 9, ⊤) :=
  .of fun i j ↦ coord (Spec (CommRingCat.of.{u} k)) (ULift.up (finProdFinEquiv (i, j)))

/-- An entry of `genericMatrix` is the corresponding affine coordinate. -/
theorem genericMatrix_apply (k : Type u) [Field k] (i j : Fin 3) :
    genericMatrix k i j =
      coord (Spec (CommRingCat.of.{u} k)) (ULift.up (finProdFinEquiv (i, j))) := sorry

/-- The set of complementary `2 × 2` minors of `genericMatrix`. -/
def twoMinors (k : Type u) [Field k] : Set Γ(AffineSpaceOverField k 9, ⊤) :=
  Set.range fun p : Fin 3 × Fin 3 ↦
    ((genericMatrix k).submatrix p.1.succAbove p.2.succAbove).det

/-- The closed rank-at-most-one locus in `AffineSpaceOverField k 9`, cut out by
the vanishing of all complementary `2 × 2` minors. -/
def rankLeOneLocus (k : Type u) [Field k] : Set (AffineSpaceOverField k 9) :=
  (AffineSpaceOverField k 9).zeroLocus (twoMinors k)

/-- The origin in `AffineSpaceOverField k 9`, cut out by the nine affine
coordinates. -/
def rankZeroLocus (k : Type u) [Field k] : Set (AffineSpaceOverField k 9) :=
  (AffineSpaceOverField k 9).zeroLocus (Set.range (coord (Spec (CommRingCat.of.{u} k))))

/-- The rank-exactly-one locus in `AffineSpaceOverField k 9`. -/
def rankOneLocus (k : Type u) [Field k] : Set (AffineSpaceOverField k 9) :=
  rankLeOneLocus k \ rankZeroLocus k

/-- The rank-at-most-one locus is Zariski closed. -/
theorem isClosed_rankLeOneLocus (k : Type u) [Field k] :
    IsClosed (rankLeOneLocus k) := sorry

/-- The origin in `AffineSpaceOverField k 9` is Zariski closed. -/
theorem isClosed_rankZeroLocus (k : Type u) [Field k] :
    IsClosed (rankZeroLocus k) := sorry

/-- The rank-exactly-one locus is Zariski locally closed. -/
theorem isLocallyClosed_rankOneLocus (k : Type u) [Field k] :
    IsLocallyClosed (rankOneLocus k) := sorry

/-- The morphism `Spec k ⟶ AffineSpaceOverField k 9` with affine coordinates `a`. -/
def homOfCoords (k : Type u) [Field k] (a : Fin 9 → k) :
    Spec (CommRingCat.of.{u} k) ⟶ AffineSpaceOverField k 9 :=
  homOfVector (𝟙 _) fun i ↦ (Scheme.ΓSpecIso (CommRingCat.of.{u} k)).inv (a i.down)

/-- A coordinate morphism `homOfCoords a` lies over `Spec k`. -/
theorem homOfCoords_comp (k : Type u) [Field k] (a : Fin 9 → k) :
    homOfCoords k a ≫ affineSpaceOverFieldHom k 9 = 𝟙 _ := sorry

/-- The closed point of `AffineSpaceOverField k 9` associated to a `3 × 3` matrix. -/
def closedPointOfMatrix (k : Type u) [Field k] (A : Matrix (Fin 3) (Fin 3) k) :
    AffineSpaceOverField k 9 :=
  homOfCoords k (coordsOfMatrix k A) (IsLocalRing.closedPoint k)

/-- The image of a matrix under `closedPointOfMatrix` is a closed point. -/
theorem isClosed_singleton_closedPointOfMatrix (k : Type u) [Field k]
    (A : Matrix (Fin 3) (Fin 3) k) :
    IsClosed {closedPointOfMatrix k A} := sorry

/-- Read a closed point of `AffineSpaceOverField k 9` as a `3 × 3` matrix over `k`. -/
def matrixOfClosedPoint (k : Type u) [Field k] [IsAlgClosed k]
    {x : AffineSpaceOverField k 9} (hx : IsClosed {x}) :
    Matrix (Fin 3) (Fin 3) k :=
  matrixOfCoords k fun t ↦
    (Scheme.ΓSpecIso (CommRingCat.of.{u} k)).hom
      ((pointOfClosedPoint (affineSpaceOverFieldHom k 9) x hx).appTop
        (coord (Spec (CommRingCat.of.{u} k)) (ULift.up t)))

/-- `matrixOfClosedPoint` recovers a matrix from its associated closed point. -/
theorem matrixOfClosedPoint_closedPointOfMatrix (k : Type u) [Field k] [IsAlgClosed k]
    (A : Matrix (Fin 3) (Fin 3) k) :
    matrixOfClosedPoint k (isClosed_singleton_closedPointOfMatrix k A) = A := sorry

/-- `closedPointOfMatrix` recovers a closed point from its associated matrix. -/
theorem closedPointOfMatrix_matrixOfClosedPoint (k : Type u) [Field k] [IsAlgClosed k]
    {x : AffineSpaceOverField k 9} (hx : IsClosed {x}) :
    closedPointOfMatrix k (matrixOfClosedPoint k hx) = x := sorry

/-- A closed point of `AffineSpaceOverField k 9` lies in `rankOneLocus` if and only
if the associated matrix has rank `1`. -/
theorem mem_rankOneLocus_closedPoint_iff (k : Type u) [Field k] [IsAlgClosed k]
    {x : AffineSpaceOverField k 9} (hx : IsClosed {x}) :
    x ∈ rankOneLocus k ↔ (matrixOfClosedPoint k hx).rank = 1 := sorry

/-- Over an algebraically closed field, the closed points of the rank-one locus
are exactly the points represented by rank-one matrices. -/
theorem closedPoints_rankOneLocus (k : Type u) [Field k] [IsAlgClosed k] :
    rankOneLocus k ∩ closedPoints (AffineSpaceOverField k 9) =
      closedPointOfMatrix k '' rankOneMatrices k := sorry

/-- The rank-exactly-one locus in affine `9`-space over an algebraically closed
field is irreducible. -/
theorem isIrreducible_rankOneLocus (k : Type u) [Field k] [IsAlgClosed k] :
    IsIrreducible (rankOneLocus k) := sorry

/-- The rank-exactly-one locus in affine `9`-space over an algebraically closed
field has topological Krull dimension `5`. -/
theorem topologicalKrullDim_rankOneLocus (k : Type u) [Field k] [IsAlgClosed k] :
    topologicalKrullDim (rankOneLocus k : Set (AffineSpaceOverField k 9)) = (5 : WithBot ℕ∞) := sorry

end AlgebraicGeometry.AffineSpace
