/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Ideal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Subspace.LocallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion.Composition

/-!
# Fitting loci of modules on algebraic spaces

Fitting ideals cut out closed subspaces, complementary open subspaces, and
successive locally closed rank loci.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The closed subspace cut out by the `r`th Fitting ideal of a module. -/
def fittingClosedSubspace (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ) : ClosedSubspace X :=
  ClosedSubspace.ofQuasiCoherentIdeal (fittingIdealSheaf F r)

/-- The defining ideal of the Fitting closed subspace is the Fitting ideal sheaf. -/
theorem fittingClosedSubspace_idealSheaf (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (r : ℕ) :
    (fittingClosedSubspace F r).idealSheaf = fittingIdealSheaf F r :=
  ClosedSubspace.ofQuasiCoherentIdeal_idealSheaf (fittingIdealSheaf F r)

/-- The Fitting closed subspaces form a descending sequence on points. -/
theorem fittingClosedSubspace_pointsSet_antitone (F : X.Modules)
    [F.IsFiniteType] [F.IsQuasicoherent] (r : ℕ) :
    (fittingClosedSubspace F (r + 1)).pointsSet ⊆
      (fittingClosedSubspace F r).pointsSet :=
  sorry

namespace fittingClosedSubspace

/-- The Fitting closed subspace of index `-1` is the ambient algebraic space. -/
def negOne (X : AlgebraicSpace S) : ClosedSubspace X :=
  ClosedSubspace.id X

/-- The underlying point-set of the index `-1` Fitting closed subspace is all points. -/
theorem negOne_pointsSet (X : AlgebraicSpace S) :
    (negOne X).pointsSet = Set.univ := by
  change Set.range (Points.map (𝟙 X)) = Set.univ
  apply Set.eq_univ_of_forall
  intro x
  exact ⟨x, Points.map_id x⟩

end fittingClosedSubspace

/-- The open complement of the closed subspace cut out by the `r`th Fitting ideal. -/
def fittingOpenComplement (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ) : OpenSubspace X :=
  OpenSubspace.fromOpens
    (Opens.mk (fittingClosedSubspace F r).pointsSetᶜ
      (fittingClosedSubspace F r).isClosed_pointsSet.isOpen_compl)

/-- The point-set of the Fitting open complement is the complement of the closed locus. -/
theorem fittingOpenComplement_pointsSet (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (r : ℕ) :
    (fittingOpenComplement F r).pointsSet =
      (fittingClosedSubspace F r).pointsSetᶜ :=
  OpenSubspace.fromOpens_pointsSet
    (Opens.mk (fittingClosedSubspace F r).pointsSetᶜ
      (fittingClosedSubspace F r).isClosed_pointsSet.isOpen_compl)

/-- The locally closed Fitting rank locus is the difference of successive closed loci,
with the ambient space as the closed locus of index `-1`. -/
def fittingRankLocus (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
    (r : ℕ) : LocallyClosedSubspace X :=
  match r with
  | 0 => (fittingOpenComplement F 0).toLocallyClosed
  | r + 1 =>
      { X := pullback (fittingOpenComplement F (r + 1)).ι
            (fittingClosedSubspace F r).ι
        ι := pullback.snd (fittingOpenComplement F (r + 1)).ι
            (fittingClosedSubspace F r).ι ≫
          (fittingClosedSubspace F r).ι
        isImmersion :=
          @IsImmersion.comp S _ _ _
            (pullback.snd (fittingOpenComplement F (r + 1)).ι
              (fittingClosedSubspace F r).ι)
            (fittingClosedSubspace F r).ι
            (IsImmersion.pullback_snd
              (@IsImmersion.ofIsOpenImmersion S _ _ _
                (fittingOpenComplement F (r + 1)).isOpenImmersion)
              (fittingClosedSubspace F r).ι)
            (@IsImmersion.ofIsClosedImmersion S _ _ _
              (fittingClosedSubspace F r).isClosedImmersion) }

/-- The rank-zero Fitting locus is the open complement of the zeroth closed locus. -/
theorem fittingRankLocus_zero (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] :
    fittingRankLocus F 0 = (fittingOpenComplement F 0).toLocallyClosed :=
  rfl

/-- The inclusion of the successor rank locus is the open-in-closed pullback inclusion. -/
theorem fittingRankLocus_succ_isPullback (F : X.Modules) [F.IsFiniteType]
    [F.IsQuasicoherent] (r : ℕ) :
    (fittingRankLocus F (r + 1)).ι =
      pullback.snd (fittingOpenComplement F (r + 1)).ι
          (fittingClosedSubspace F r).ι ≫
        (fittingClosedSubspace F r).ι :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
