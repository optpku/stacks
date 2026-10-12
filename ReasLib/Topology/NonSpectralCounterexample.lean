/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Basic
public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import ReasLib.Topology.Category.TopCat.Subset

@[expose] public section

open CategoryTheory Opposite Set TopCat TopologicalSpace

noncomputable section

universe u

namespace Topology.NonSpectralCounterexample

/-- The closed subsets prescribed for the disjoint union `Y ⊕ Unit`. -/
def counterexampleClosedFamily {Y : Type u} [TopologicalSpace Y] (y : Y) :
    Set (Set (Y ⊕ Unit)) :=
  ({∅, {Sum.inl y}} : Set (Set (Y ⊕ Unit))) ∪
    {S | ∃ F : Set Y, IsClosed F ∧ S = Sum.inl '' F ∪ {Sum.inr ()}}

/-- The empty set belongs to the prescribed closed-set family. -/
theorem counterexampleClosedFamily_empty {Y : Type u} [TopologicalSpace Y] (y : Y) :
    ∅ ∈ counterexampleClosedFamily y := sorry

/-- Arbitrary intersections of prescribed closed sets remain prescribed closed sets. -/
theorem counterexampleClosedFamily_sInter {Y : Type u} [TopologicalSpace Y] [T1Space Y] (y : Y)
    (A : Set (Set (Y ⊕ Unit))) (hA : A ⊆ counterexampleClosedFamily y) :
    ⋂₀ A ∈ counterexampleClosedFamily y := sorry

/-- Finite unions of prescribed closed sets remain prescribed closed sets. -/
theorem counterexampleClosedFamily_union {Y : Type u} [TopologicalSpace Y] [T1Space Y] (y : Y)
    (A : Set (Y ⊕ Unit)) (hA : A ∈ counterexampleClosedFamily y)
    (B : Set (Y ⊕ Unit)) (hB : B ∈ counterexampleClosedFamily y) :
    A ∪ B ∈ counterexampleClosedFamily y := sorry

/-- The topology on `Y ⊕ Unit` whose closed sets are prescribed by the family above. -/
@[implicit_reducible]
def counterexampleTopology {Y : Type u} [TopologicalSpace Y] [T1Space Y] (y : Y) :
    TopologicalSpace (Y ⊕ Unit) :=
  TopologicalSpace.ofClosed (counterexampleClosedFamily y)
    (counterexampleClosedFamily_empty y)
    (counterexampleClosedFamily_sInter y)
    (fun A hA B hB ↦ counterexampleClosedFamily_union y A hA B hB)

/-- The bundled topological space `X = Y ⊕ {x}` used in the construction. -/
def counterexampleSpace {Y : Type u} [TopologicalSpace Y] [T1Space Y] (y : Y) : TopCat.{u} :=
  @TopCat.of (Y ⊕ Unit) (counterexampleTopology y)

/-- The extra point adjoined to `Y` in the counterexample space. -/
def counterexampleExtraPoint {Y : Type u} : Y ⊕ Unit := Sum.inr ()

/-- The point of the counterexample space corresponding to the chosen point `y : Y`. -/
def counterexampleYPoint {Y : Type u} (y : Y) : Y ⊕ Unit := Sum.inl y

/-- The closed subset `Z = {x, y}` in the counterexample space. -/
def counterexampleClosedSubset {Y : Type u} (y : Y) : Set (Y ⊕ Unit) :=
  {counterexampleExtraPoint, counterexampleYPoint y}

/-- A universe-correct representative of a two-element value type. -/
abbrev counterexampleValue : Type u := ULift.{u} Bool

/-- The constant two-valued sheaf on the counterexample space. -/
noncomputable def counterexampleConstantSheaf {Y : Type u} [TopologicalSpace Y]
    [T1Space Y] (y : Y) : (counterexampleSpace y).Sheaf (Type u) :=
  (constantSheaf (Opens.grothendieckTopology (counterexampleSpace y)) (Type u)).obj
    counterexampleValue

/-- The distinguished closed subset is closed in the constructed topology. -/
theorem counterexampleClosedSubset_isClosed {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    (y : Y) (hy : ¬ IsOpen ({y} : Set Y)) :
    @IsClosed (Y ⊕ Unit) (counterexampleTopology y) (counterexampleClosedSubset y) := sorry

/-- Every intersection of the distinguished subset with a point closure is connected. -/
theorem counterexampleClosedSubset_closure_inter_isConnected {Y : Type u}
    [TopologicalSpace Y] [T1Space Y] (y : Y) (hy : ¬ IsOpen ({y} : Set Y)) :
    ∀ z : Y ⊕ Unit,
      @IsConnected (Y ⊕ Unit) (counterexampleTopology y)
        (counterexampleClosedSubset y ∩
          @closure (Y ⊕ Unit) (counterexampleTopology y) ({z} : Set (Y ⊕ Unit))) := sorry

/-- The constructed ambient topological space is connected. -/
theorem counterexampleSpace_isConnected {Y : Type u} [TopologicalSpace Y] [T1Space Y]
    (y : Y) (hy : ¬ IsOpen ({y} : Set Y)) :
    @IsConnected (Y ⊕ Unit) (counterexampleTopology y) Set.univ := sorry

/-- The distinguished closed subset is not connected. -/
theorem counterexampleClosedSubset_not_isConnected {Y : Type u} [TopologicalSpace Y]
    [T1Space Y] (y : Y) (hy : ¬ IsOpen ({y} : Set Y)) :
    ¬ @IsConnected (Y ⊕ Unit) (counterexampleTopology y) (counterexampleClosedSubset y) := sorry

/-- The restriction map on global sections of the constant sheaf is not bijective. -/
theorem counterexampleConstantSheaf_restriction_not_bijective {Y : Type u}
    [TopologicalSpace Y] [T1Space Y] (y : Y) (hy : ¬ IsOpen ({y} : Set Y)) :
    ¬ Function.Bijective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
        (TopCat.subsetInclusion (counterexampleClosedSubset y))).unit.app
        (counterexampleConstantSheaf y)).hom.app (op (⊤ : Opens (counterexampleSpace y)))) := sorry

end Topology.NonSpectralCounterexample

end
