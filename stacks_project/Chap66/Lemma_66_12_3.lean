/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Construction
public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Definition_66_7_2
public import stacks_project.Chap66.Remark_66_7_3_EtaleLocal

/-!
# Reduced closed subspaces of algebraic spaces

A closed subset `T ⊂ |X|` of the points of an algebraic space is the underlying
point-set of a unique reduced closed subspace `Z ⊂ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

/-- Lemma 66.12.3: let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`T ⊂ |X|` be a closed subset. There exists a unique closed subspace `Z ⊂ X` with
`Z.pointsSet = T` (i.e. `|Z| = T`) and with `Z` reduced, in the sense that
`hasEtaleLocal IsReduced` holds on `Z.X`. Uniqueness is a unique morphism over `X`. -/
@[stacks 03IQ]
theorem exists_reduced {S : Scheme.{u}} {X : AlgebraicSpace S}
    (T : Set (Points X)) (hT : IsClosed T) :
    ∃ Z : ClosedSubspace X,
      Z.pointsSet = T ∧
        hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z.X ∧
          ∀ Z' : ClosedSubspace X, Z'.pointsSet = T →
            hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z'.X →
              ∃! f : Z'.X ⟶ Z.X, f ≫ Z.ι = Z'.ι :=
  ReducedClosed.Construction.exists_reduced X ⟨T, hT⟩

/-- Any two reduced closed subspaces of `X` with the same underlying point-set admit a unique
morphism over `X`. -/
theorem unique {S : Scheme.{u}} {X : AlgebraicSpace S} {Z Z' : ClosedSubspace X}
    (h_eq : Z.pointsSet = Z'.pointsSet)
    (hZ : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z.X)
    (hZ' : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z'.X) :
    ∃! f : Z.X ⟶ Z'.X, f ≫ Z'.ι = Z.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace
