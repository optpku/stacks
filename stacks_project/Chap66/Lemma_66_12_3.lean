module

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

/-- The underlying set of points of a closed subspace, as the image of `|Z| → |X|`. -/
def pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) :
    Set (Points X) :=
  Set.range (Points.map Z.ι)

/-- `pointsSet Z` is the range of `Points.map Z.ι`. -/
theorem pointsSet_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) :
    Z.pointsSet = Set.range (Points.map Z.ι) :=
  sorry

/-- A point of `|X|` lies in `pointsSet Z` if and only if it is the image of a point of `|Z|`. -/
theorem mem_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X)
    {x : Points X} :
    x ∈ Z.pointsSet ↔ ∃ y : Points Z.X, Points.map Z.ι y = x :=
  sorry

/-- The image `|Z| ⊆ |X|` is closed in the canonical topology on `|X|`. -/
theorem isClosed_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (Z : ClosedSubspace X) :
    IsClosed (Z.pointsSet : Set (Points X)) :=
  sorry

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
  sorry

/-- Any two reduced closed subspaces of `X` with the same underlying point-set admit a unique
morphism over `X`. -/
theorem unique {S : Scheme.{u}} {X : AlgebraicSpace S} {Z Z' : ClosedSubspace X}
    (h_eq : Z.pointsSet = Z'.pointsSet)
    (hZ : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z.X)
    (hZ' : hasEtaleLocal (AlgebraicGeometry.IsReduced : ObjectProperty Scheme.{u}) Z'.X) :
    ∃! f : Z.X ⟶ Z'.X, f ≫ Z'.ι = Z.ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace
