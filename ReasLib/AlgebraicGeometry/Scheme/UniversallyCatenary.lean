/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.Topology.Catenary

@[expose] public section

namespace AlgebraicGeometry

universe u

open TopologicalSpace

/-- A scheme is universally catenary if it is locally Noetherian and every scheme locally of
finite type over it is catenary. -/
class UniversallyCatenary (S : Scheme.{u}) : Prop extends IsLocallyNoetherian S where
  /-- Every scheme locally of finite type over a universally catenary scheme is catenary. -/
  catenarySpace_of_locallyOfFiniteType {X : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    CatenarySpace X

/-- A scheme is universally catenary exactly when it is locally Noetherian and every scheme
locally of finite type over it is catenary. -/
theorem universallyCatenary_iff (S : Scheme.{u}) :
    UniversallyCatenary S ↔ IsLocallyNoetherian S ∧
      ∀ {X : Scheme.{u}} (f : X ⟶ S), LocallyOfFiniteType f → CatenarySpace X := sorry

/-- A scheme locally of finite type over a universally catenary scheme is universally
catenary. -/
theorem universallyCatenary_of_locallyOfFiniteType {S X : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] : UniversallyCatenary X := sorry

/-- Every open subscheme of a universally catenary scheme is universally catenary. -/
instance instUniversallyCatenaryToScheme {S : Scheme.{u}} [UniversallyCatenary S]
    (U : S.Opens) : UniversallyCatenary U.toScheme := by
  simpa using universallyCatenary_of_locallyOfFiniteType U.ι

/-- Universal catenarity restricts to every open subscheme. -/
theorem UniversallyCatenary.toScheme {S : Scheme.{u}} [hS : UniversallyCatenary S]
    (U : S.Opens) : UniversallyCatenary U.toScheme :=
  inferInstance

/-- The underlying topological space of a universally catenary scheme is catenary. -/
instance instCatenarySpaceOfUniversallyCatenary (S : Scheme.{u}) [h : UniversallyCatenary S] :
    CatenarySpace S :=
  h.catenarySpace_of_locallyOfFiniteType (CategoryTheory.CategoryStruct.id S)

end AlgebraicGeometry
