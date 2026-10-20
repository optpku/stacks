/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Subobject
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Sober
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Separation

/-!
# Integral closed subspaces and irreducible closed subsets

Integral closed subobjects of a decent algebraic space correspond to irreducible
closed subsets of its space of points, with inverse given by reduced induced structures.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ClosedSubspace

/-- The reduced induced closed subspace on an irreducible closed subset. -/
abbrev ofIrreducibleClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (T : IrreducibleCloseds (Points X)) : ClosedSubspace X where
  X := ReducedClosed.Space.space X (Closeds.mk (T : Set (Points X)) T.isClosed)
  ι := (ClosedSubspaceStructure.reduced (Closeds.mk (T : Set (Points X)) T.isClosed)).ι
  isClosedImmersion :=
    (ClosedSubspaceStructure.reduced
      (Closeds.mk (T : Set (Points X)) T.isClosed)).subspace.isClosedImmersion

/-- The support of the reduced induced closed subspace is the original subset. -/
theorem pointsSet_ofIrreducibleClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (T : IrreducibleCloseds (Points X)) :
    (ofIrreducibleClosed T).pointsSet = (T : Set (Points X)) :=
  sorry

/-- The reduced induced closed subspace on an irreducible closed subset is integral
and has the prescribed support. -/
theorem ofIrreducibleClosed_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (T : IrreducibleCloseds (Points X)) :
    IsIntegral (ofIrreducibleClosed T).X ∧
      (ofIrreducibleClosed T).pointsSet = (T : Set (Points X)) :=
  ⟨inferInstance, pointsSet_ofIrreducibleClosed T⟩

/-- The image of an integral closed subspace on points is irreducible. -/
theorem isIrreducible_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsIntegral Z.X] :
    _root_.IsIrreducible Z.pointsSet :=
  sorry

/-- The irreducible closed subset underlying an integral closed subspace. -/
def irreducibleClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsIntegral Z.X] : IrreducibleCloseds (Points X) :=
  IrreducibleCloseds.mk Z.pointsSet (isIrreducible_pointsSet Z) (isClosed_pointsSet Z)

/-- The support of the irreducible closed subset of an integral closed subspace
is its underlying point-set. -/
theorem coe_irreducibleClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Z : ClosedSubspace X) [IsIntegral Z.X] :
    (irreducibleClosed Z : Set (Points X)) = Z.pointsSet := rfl

/-- An integral closed subspace of a decent algebraic space admits a unique morphism
over the ambient space to the reduced induced structure on its support. -/
theorem existsUnique_hom_ofIrreducibleClosed {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (Z : ClosedSubspace X) [IsIntegral Z.X] :
    ∃! f : Z.X ⟶ (ofIrreducibleClosed (irreducibleClosed Z)).X,
      f ≫ (ofIrreducibleClosed (irreducibleClosed Z)).ι = Z.ι :=
  sorry

end ClosedSubspace

/-- Integral closed subspaces are subobjects admitting an integral closed-immersion
representative, identifying presentations isomorphic over the ambient space. -/
def IntegralClosedSubspaces {S : Scheme.{u}} (X : AlgebraicSpace S) :=
  {P : Subobject X // ∃ Z : ClosedSubspace X, IsIntegral Z.X ∧ Z.toSubobject = P}

namespace IntegralClosedSubspaces

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- An integral closed-immersion presentation determines an integral closed subobject. -/
def mk (Z : ClosedSubspace X) (h : IsIntegral Z.X) : IntegralClosedSubspaces X :=
  ⟨Z.toSubobject, Z, h, rfl⟩

/-- The support of an integral closed subobject, computed independently of its presentation. -/
def pointsSet (P : IntegralClosedSubspaces X) : Set (Points X) :=
  subobjectPointsSet P.val

/-- The support of an integral closed subobject is closed. -/
theorem isClosed_pointsSet (P : IntegralClosedSubspaces X) : IsClosed P.pointsSet := by
  obtain ⟨Z, hZ, h⟩ := P.property
  change IsClosed (subobjectPointsSet P.val)
  rw [← h, ClosedSubspace.subobjectPointsSet_toSubobject]
  exact Z.isClosed_pointsSet

/-- The support of an integral closed subobject is irreducible. -/
theorem isIrreducible_pointsSet (P : IntegralClosedSubspaces X) :
    _root_.IsIrreducible P.pointsSet := by
  obtain ⟨Z, hZ, h⟩ := P.property
  change _root_.IsIrreducible (subobjectPointsSet P.val)
  rw [← h, ClosedSubspace.subobjectPointsSet_toSubobject]
  exact @ClosedSubspace.isIrreducible_pointsSet _ _ Z hZ

/-- An integral closed subobject determines its irreducible closed support. -/
def irreducibleClosed (P : IntegralClosedSubspaces X) : IrreducibleCloseds (Points X) :=
  IrreducibleCloseds.mk P.pointsSet P.isIrreducible_pointsSet P.isClosed_pointsSet

/-- The support map on a represented integral closed subobject is the representative's
underlying point-set. -/
theorem coe_irreducibleClosed_mk (Z : ClosedSubspace X) (h : IsIntegral Z.X) :
    (irreducibleClosed (mk Z h) : Set (Points X)) = Z.pointsSet :=
  Z.subobjectPointsSet_toSubobject

/-- An irreducible closed subset determines the integral subobject of its reduced
induced closed subspace. -/
def ofIrreducibleClosed [IsDecent X] (T : IrreducibleCloseds (Points X)) :
    IntegralClosedSubspaces X :=
  mk (ClosedSubspace.ofIrreducibleClosed T) inferInstance

/-- The reduced induced structure on the support of an integral closed subobject
represents that same subobject. -/
theorem ofIrreducibleClosed_irreducibleClosed [IsDecent X] (P : IntegralClosedSubspaces X) :
    ofIrreducibleClosed (irreducibleClosed P) = P :=
  sorry

/-- The support of the reduced induced integral closed subobject is the original
irreducible closed subset. -/
theorem irreducibleClosed_ofIrreducibleClosed [IsDecent X]
    (T : IrreducibleCloseds (Points X)) :
    irreducibleClosed (ofIrreducibleClosed T) = T :=
  sorry

/-- Integral closed subobjects of a decent algebraic space correspond to its
irreducible closed subsets via support and reduced induced structure. -/
def equivIrreducibleCloseds [IsDecent X] :
    IntegralClosedSubspaces X ≃ IrreducibleCloseds (Points X) where
  toFun := irreducibleClosed
  invFun := ofIrreducibleClosed
  left_inv := ofIrreducibleClosed_irreducibleClosed
  right_inv := irreducibleClosed_ofIrreducibleClosed

end IntegralClosedSubspaces

/-- For a decent algebraic space, singleton closure bijects points with irreducible
closed subsets, and support bijects integral closed subobjects with those subsets.
On a closed-immersion representative, the support map is the image on points. -/
theorem canonicalBijections {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X] :
    Function.Bijective
      (irreducibleSetEquivPoints.toEquiv.symm : Points X ≃ IrreducibleCloseds (Points X)) ∧
    Function.Bijective
      (IntegralClosedSubspaces.irreducibleClosed :
        IntegralClosedSubspaces X → IrreducibleCloseds (Points X)) ∧
    (∀ x : Points X,
      (irreducibleSetEquivPoints.toEquiv.symm x : Set (Points X)) = closure {x}) ∧
    (∀ (Z : ClosedSubspace X) (h : IsIntegral Z.X),
      (IntegralClosedSubspaces.irreducibleClosed (IntegralClosedSubspaces.mk Z h) :
        Set (Points X)) = Z.pointsSet) :=
  ⟨irreducibleSetEquivPoints.toEquiv.symm.bijective,
    IntegralClosedSubspaces.equivIrreducibleCloseds.bijective,
    coe_irreducibleEquivPoints_symm_apply,
    IntegralClosedSubspaces.coe_irreducibleClosed_mk⟩

/-- Every point of a decent algebraic space is the generic point of an integral
closed subspace, unique up to a unique morphism over the ambient space. -/
theorem existsUnique_integralClosedSubspace {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (ξ : Points X) :
    ∃ Z : ClosedSubspace X,
      IsIntegral Z.X ∧
        IsGenericPoint ξ Z.pointsSet ∧
          ∀ (Z' : ClosedSubspace X),
            IsIntegral Z'.X →
              IsGenericPoint ξ Z'.pointsSet →
                ∃! g : Z'.X ⟶ Z.X, g ≫ Z.ι = Z'.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
