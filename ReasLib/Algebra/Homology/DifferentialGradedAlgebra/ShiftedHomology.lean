/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedAlgebra.Predifferential

/-!
# Shifted maps on homology

A homogeneous map of degree `k` that graded-commutes with the differential sends degree-`n`
cycles and homology classes to degree `n + k`.  The construction is made through an explicit
morphism between the corresponding Mathlib short complexes, with the Koszul sign placed on its
outer components.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

variable {R : Type u} [CommRing R]

namespace ChainGradedAlgebra.HomogeneousMap

variable {A : ChainDGAlgebra.{u, v} R} {k n m : ℤ}

/-- Translation by `k` commutes with the predecessor index of a chain complex. -/
theorem shiftPrevIndex (n k : ℤ) :
    (ComplexShape.down ℤ).prev n + k =
      (ComplexShape.down ℤ).prev (n + k) := sorry

/-- Translation by `k` commutes with the successor index of a chain complex. -/
theorem shiftNextIndex (n k : ℤ) :
    (ComplexShape.down ℤ).next n + k =
      (ComplexShape.down ℤ).next (n + k) := sorry

/-- The signed predecessor component used by the short-complex map of a homogeneous map. -/
def shortComplexPrevMap
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k) (n : ℤ) :
    A.toChainGradedAlgebra.X ((ComplexShape.down ℤ).prev n) →ₗ[R]
      A.toChainGradedAlgebra.X ((ComplexShape.down ℤ).prev (n + k)) :=
  k.negOnePow •
    (A.toChainGradedAlgebra.reindex (shiftPrevIndex n k)).comp
      (D ((ComplexShape.down ℤ).prev n))

/-- The signed successor component used by the short-complex map of a homogeneous map. -/
def shortComplexNextMap
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k) (n : ℤ) :
    A.toChainGradedAlgebra.X ((ComplexShape.down ℤ).next n) →ₗ[R]
      A.toChainGradedAlgebra.X ((ComplexShape.down ℤ).next (n + k)) :=
  k.negOnePow •
    (A.toChainGradedAlgebra.reindex (shiftNextIndex n k)).comp
      (D ((ComplexShape.down ℤ).next n))

/-- The predecessor component of a graded-commuting homogeneous map commutes with the first
arrow of the homology short complex. -/
theorem shortComplexMap_comm₁₂
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.HomogeneousMap.GradedCommutes D
      (ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential))
    (n : ℤ) :
    ModuleCat.ofHom (shortComplexPrevMap D n) ≫ (A.toChainComplex.sc (n + k)).f =
      (A.toChainComplex.sc n).f ≫ ModuleCat.ofHom (D n) := sorry

/-- The successor component of a graded-commuting homogeneous map commutes with the second
arrow of the homology short complex. -/
theorem shortComplexMap_comm₂₃
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.HomogeneousMap.GradedCommutes D
      (ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential))
    (n : ℤ) :
    ModuleCat.ofHom (D n) ≫ (A.toChainComplex.sc (n + k)).g =
      (A.toChainComplex.sc n).g ≫ ModuleCat.ofHom (shortComplexNextMap D n) := sorry

/-- A degree-`k` homogeneous map graded-commuting with the differential gives a morphism from the
degree-`n` homology short complex to the degree-`n + k` homology short complex. -/
def shortComplexMap
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.HomogeneousMap.GradedCommutes D
      (ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential))
    (n : ℤ) :
    A.toChainComplex.sc n ⟶ A.toChainComplex.sc (n + k) where
  τ₁ := ModuleCat.ofHom (shortComplexPrevMap D n)
  τ₂ := ModuleCat.ofHom (D n)
  τ₃ := ModuleCat.ofHom (shortComplexNextMap D n)
  comm₁₂ := shortComplexMap_comm₁₂ D hD n
  comm₂₃ := shortComplexMap_comm₂₃ D hD n

/-- The middle component of the shifted short-complex map is the original homogeneous map. -/
@[simp]
theorem shortComplexMap_τ₂
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.HomogeneousMap.GradedCommutes D
      (ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential))
    (n : ℤ) :
    (shortComplexMap D hD n).τ₂ = ModuleCat.ofHom (D n) := sorry

/-- The map on cycles induced by a closed homogeneous map of arbitrary degree. -/
noncomputable def cyclesMap
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.HomogeneousMap.GradedCommutes D
      (ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential))
    (n : ℤ) :
    A.cycles n →ₗ[R] A.cycles (n + k) :=
  (ShortComplex.cyclesMap (shortComplexMap D hD n)).hom

/-- 09PT: The map on homology induced by a closed homogeneous map of arbitrary degree. -/
@[stacks 09PT "homology map induced by a closed homogeneous map"]
noncomputable def homologyMap
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.HomogeneousMap.GradedCommutes D
      (ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential))
    (n : ℤ) :
    A.homology n →ₗ[R] A.homology (n + k) :=
  (ShortComplex.homologyMap (shortComplexMap D hD n)).hom

/-- Transport the cycle map of a degree-`k` homogeneous map to a specified target degree. -/
noncomputable def cyclesMapTo
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.HomogeneousMap.GradedCommutes D
      (ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential))
    (h : n + k = m) :
    A.cycles n →ₗ[R] A.cycles m :=
  h ▸ cyclesMap D hD n

/-- Transport the homology map of a degree-`k` homogeneous map to a specified target degree. -/
noncomputable def homologyMapTo
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.HomogeneousMap.GradedCommutes D
      (ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential))
    (h : n + k = m) :
    A.homology n →ₗ[R] A.homology m :=
  h ▸ homologyMap D hD n

/-- On representatives, the induced cycle map is the original homogeneous map. -/
@[simp]
theorem cyclesMap_iCycles
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.HomogeneousMap.GradedCommutes D
      (ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential))
    (n : ℤ) (x : A.cycles n) :
    A.iCycles (n + k) (cyclesMap D hD n x) =
      D n (A.iCycles n x) := sorry

/-- On a cycle class, the induced homology map is represented by the original homogeneous map. -/
@[simp]
theorem homologyMap_homologyπ
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.HomogeneousMap.GradedCommutes D
      (ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential))
    (n : ℤ) (x : A.cycles n) :
    homologyMap D hD n (A.homologyπ n x) =
      A.homologyπ (n + k) (cyclesMap D hD n x) := sorry

/-- The transported cycle map still applies the original homogeneous map to representatives. -/
@[simp]
theorem cyclesMapTo_iCycles
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.HomogeneousMap.GradedCommutes D
      (ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential))
    (h : n + k = m) (x : A.cycles n) :
    A.iCycles m (cyclesMapTo D hD h x) =
      A.toChainGradedAlgebra.reindex h (D n (A.iCycles n x)) := sorry

/-- The transported homology map sends a cycle class to its transported image class. -/
@[simp]
theorem homologyMapTo_homologyπ
    (D : ChainGradedAlgebra.HomogeneousMap A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.HomogeneousMap.GradedCommutes D
      (ChainGradedAlgebra.Derivation.toHomogeneousMap A.predifferential))
    (h : n + k = m) (x : A.cycles n) :
    homologyMapTo D hD h (A.homologyπ n x) =
      A.homologyπ m (cyclesMapTo D hD h x) := sorry

end ChainGradedAlgebra.HomogeneousMap

namespace ChainGradedAlgebra.Derivation

variable {A : ChainDGAlgebra.{u, v} R} {k n m : ℤ}

/-- The map on cycles induced by a degree-`k` derivation closed under the chain differential. -/
noncomputable def cyclesMap
    (D : ChainGradedAlgebra.Derivation A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.Derivation.IsClosed D A.predifferential)
    (n : ℤ) :
    A.cycles n →ₗ[R] A.cycles (n + k) :=
  ChainGradedAlgebra.HomogeneousMap.cyclesMap
    (ChainGradedAlgebra.Derivation.toHomogeneousMap D) hD n

/-- The map on homology induced by a degree-`k` derivation closed under the chain differential. -/
@[stacks 09PT "homology action of a closed graded derivation"]
noncomputable def homologyMap
    (D : ChainGradedAlgebra.Derivation A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.Derivation.IsClosed D A.predifferential)
    (n : ℤ) :
    A.homology n →ₗ[R] A.homology (n + k) :=
  ChainGradedAlgebra.HomogeneousMap.homologyMap
    (ChainGradedAlgebra.Derivation.toHomogeneousMap D) hD n

/-- Transport the cycle map of a closed degree-`k` derivation to a specified target degree. -/
noncomputable def cyclesMapTo
    (D : ChainGradedAlgebra.Derivation A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.Derivation.IsClosed D A.predifferential)
    (h : n + k = m) :
    A.cycles n →ₗ[R] A.cycles m :=
  ChainGradedAlgebra.HomogeneousMap.cyclesMapTo
    (ChainGradedAlgebra.Derivation.toHomogeneousMap D) hD h

/-- Transport the homology map of a closed degree-`k` derivation to a specified target degree. -/
noncomputable def homologyMapTo
    (D : ChainGradedAlgebra.Derivation A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.Derivation.IsClosed D A.predifferential)
    (h : n + k = m) :
    A.homology n →ₗ[R] A.homology m :=
  ChainGradedAlgebra.HomogeneousMap.homologyMapTo
    (ChainGradedAlgebra.Derivation.toHomogeneousMap D) hD h

/-- A closed derivation acts on representatives through its underlying homogeneous map. -/
@[simp]
theorem cyclesMap_iCycles
    (D : ChainGradedAlgebra.Derivation A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.Derivation.IsClosed D A.predifferential)
    (n : ℤ) (x : A.cycles n) :
    A.iCycles (n + k) (ChainGradedAlgebra.Derivation.cyclesMap D hD n x) =
      D n (A.iCycles n x) := sorry

/-- The homology action of a closed derivation sends a cycle class to the class of its image. -/
@[simp]
theorem homologyMap_homologyπ
    (D : ChainGradedAlgebra.Derivation A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.Derivation.IsClosed D A.predifferential)
    (n : ℤ) (x : A.cycles n) :
    ChainGradedAlgebra.Derivation.homologyMap D hD n (A.homologyπ n x) =
      A.homologyπ (n + k) (ChainGradedAlgebra.Derivation.cyclesMap D hD n x) := sorry

/-- The transported homology action of a closed derivation has the expected cycle-class formula. -/
@[simp]
theorem homologyMapTo_homologyπ
    (D : ChainGradedAlgebra.Derivation A.toChainGradedAlgebra k)
    (hD : ChainGradedAlgebra.Derivation.IsClosed D A.predifferential)
    (h : n + k = m) (x : A.cycles n) :
    ChainGradedAlgebra.Derivation.homologyMapTo D hD h (A.homologyπ n x) =
      A.homologyπ m (ChainGradedAlgebra.Derivation.cyclesMapTo D hD h x) := sorry

end ChainGradedAlgebra.Derivation
