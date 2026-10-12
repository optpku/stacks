/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.ResidualConstruction
public import stacks_project.Chap70.Lemma_70_5_4_PointClosure
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints

/-! # The concrete reduced point closure in the quasi-separated source range

Its reduced atlas is the direct public owner. Its decency certificate
contains the explicitly descended equalizer-field point. No broad
unconditional point-closure integrality instance is introduced.
-/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicSpace.PointClosure

variable {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X)

def pointMap (z : Points (space x)) : closedSubset x :=
  ⟨Points.map (ι x) z, by
    change Points.map (ι x) z ∈ (closedSubset x : Set (Points X))
    rw [← range_ι x]
    exact Set.mem_range_self z⟩

theorem pointMap_bijective : Function.Bijective (pointMap x) := by
  sorry

def pointEquiv : Points (space x) ≃ closedSubset x :=
  Equiv.ofBijective (pointMap x) (pointMap_bijective x)

def originalPoint : closedSubset x := ⟨x, subset_closure (Set.mem_singleton x)⟩
def generic : Points (space x) := (pointEquiv x).symm (originalPoint x)

theorem generic_maps_to_original : Points.map (ι x) (generic x) = x :=
  congrArg Subtype.val ((pointEquiv x).apply_symm_apply (originalPoint x))

theorem generic_mem : generic x ∈ AlgebraicSpace.genericPoints (space x) := by sorry

theorem irreducible : AlgebraicSpace.IsIrreducible (space x) := by sorry

theorem quasiSeparated [AlgebraicSpace.IsQuasiSeparated X] :
    AlgebraicSpace.IsQuasiSeparated (space x) := by sorry

theorem decent [AlgebraicSpace.IsQuasiSeparated X] : AlgebraicSpace.IsDecent (space x) := by
  -- Local instance justification (proof-local temporary data): The reduced closure of this point inherits quasi-separatedness; use that property to derive its decency.
  letI := quasiSeparated x
  exact ResidualPoint.decent (space x)

theorem integral [AlgebraicSpace.IsQuasiSeparated X] : AlgebraicSpace.IsIntegral (space x) where
  toIsReduced := instIsReduced_space x
  toIsDecent := decent x
  toIsIrreducible := irreducible x

end AlgebraicGeometry.AlgebraicSpace.PointClosure
