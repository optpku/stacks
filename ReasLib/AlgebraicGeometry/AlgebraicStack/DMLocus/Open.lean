/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Union
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation.Object

/-!
# Largest open DM and quasi-DM substacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- The largest open DM substack is the union of all open DM substacks. -/
def dmLocus {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Substack.Open X :=
  ⟨Substack.iUnion
      (fun U : {U : Substack.Open X // IsDM (Substack.Open.category U)} => U.val.val),
    Substack.isOpen_iUnion _ (fun U => U.val.property)⟩

/-- The largest open DM substack of an algebraic stack is DM. -/
instance instIsDMDmLocus {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] : IsDM (Substack.Open.category (dmLocus X)) := sorry

/-- Every open DM substack is contained in the largest open DM substack on points. -/
theorem dmLocus_maximal {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (V : Substack.Open X) (hV : IsDM (Substack.Open.category V)) :
    V.pointsSet ⊆ (dmLocus X).pointsSet := sorry

/-- A point lies on the largest open DM substack exactly when it lies on an open DM substack. -/
theorem dmLocus_pointsSet_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    x ∈ (dmLocus X).pointsSet ↔
      ∃ V : Substack.Open X, IsDM (Substack.Open.category V) ∧ x ∈ V.pointsSet := sorry

/-- The DM locus is DM and contains every open DM substack on points. -/
theorem dmLocus_spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsDM (Substack.Open.category (dmLocus X)) ∧
      ∀ V : Substack.Open X, IsDM (Substack.Open.category V) →
        V.pointsSet ⊆ (dmLocus X).pointsSet := sorry

/-- The largest open quasi-DM substack is the union of all open quasi-DM substacks. -/
def quasiDMLocus {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    Substack.Open X :=
  ⟨Substack.iUnion
      (fun U : {U : Substack.Open X // IsQuasiDM (Substack.Open.category U)} => U.val.val),
    Substack.isOpen_iUnion _ (fun U => U.val.property)⟩

/-- The largest open quasi-DM substack of an algebraic stack is quasi-DM. -/
instance instIsQuasiDMQuasiDMLocus {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] : IsQuasiDM (Substack.Open.category (quasiDMLocus X)) := sorry

/-- Every open quasi-DM substack is contained in the largest open quasi-DM substack on points. -/
theorem quasiDMLocus_maximal {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] (V : Substack.Open X) (hV : IsQuasiDM (Substack.Open.category V)) :
    V.pointsSet ⊆ (quasiDMLocus X).pointsSet := sorry

/-- A point lies on the largest open quasi-DM substack exactly when it lies on an open
quasi-DM substack. -/
theorem quasiDMLocus_pointsSet_iff {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] {x : Points X} :
    x ∈ (quasiDMLocus X).pointsSet ↔
      ∃ V : Substack.Open X, IsQuasiDM (Substack.Open.category V) ∧ x ∈ V.pointsSet := sorry

/-- The quasi-DM locus is quasi-DM and contains every open quasi-DM substack on points. -/
theorem quasiDMLocus_spec {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X] :
    IsQuasiDM (Substack.Open.category (quasiDMLocus X)) ∧
      ∀ V : Substack.Open X, IsQuasiDM (Substack.Open.category V) →
        V.pointsSet ⊆ (quasiDMLocus X).pointsSet := sorry

/-- The largest open DM substack is contained in the largest open quasi-DM substack on points. -/
theorem dmLocus_subset_quasiDMLocus {S : Scheme.{u}} (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (dmLocus X).pointsSet ⊆ (quasiDMLocus X).pointsSet := sorry

/-- The canonical inclusion of the DM locus factors through the inclusion of the quasi-DM locus. -/
theorem dmLocus_factorsThrough_quasiDMLocus {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    AlgebraicGeometry.Groupoids.Hom.FactorsThrough
      (Substack.Open.inclusion (dmLocus X))
      (Substack.Open.inclusion (quasiDMLocus X)) := sorry

end AlgebraicGeometry.AlgebraicStack
