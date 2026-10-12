/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
public import ReasLib.Topology.Specialization.Dimension

@[expose] public section

open CategoryTheory TopologicalSpace

universe u v

namespace AlgebraicGeometry.Scheme.Hom

/-- Inverse images under a scheme morphism preserve locally finite families of closed subsets
for schemes locally of finite type over a universally catenary scheme with a dimension function. -/
theorem locallyFinite_preimage
    {S X Y : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (pX : X ⟶ S) [LocallyOfFiniteType pX] (pY : Y ⟶ S) [LocallyOfFiniteType pY]
    (f : X ⟶ Y) {I : Type v} (Z : I → Closeds Y)
    (hZ : LocallyFinite (fun i ↦ (Z i : Set Y))) :
    LocallyFinite (fun i ↦ ((Z i).preimage f.continuous : Set X)) := sorry

end AlgebraicGeometry.Scheme.Hom
