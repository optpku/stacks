module

public import Mathlib.Topology.Sober
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap72.Lemma_72_4_7_IntegralClosed

/-!
# Irreducible components of closed subspaces of algebraic spaces

An integral closed subspace `Z ⊂ Y` whose point-set is an irreducible component of
`|Y|` is an irreducible component of `Y`. The canonical such subspace on a generic
point is the reduced induced structure on the closure of that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Relative to the canonical topology on points, the project's generic points of
`|X|` agree with the topological generic points. -/
theorem genericPoints_eq_topological {S : Scheme.{u}} (X : AlgebraicSpace S) :
    genericPoints X = _root_.genericPoints (Points X) :=
  sorry

namespace ClosedSubspace

/-- A closed subspace of a quasi-separated algebraic space is quasi-separated. -/
instance instIsQuasiSeparated {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiSeparated X] (Y : ClosedSubspace X) : IsQuasiSeparated Y.X :=
  sorry

/-- A closed subspace of a decent algebraic space is decent. -/
instance instIsDecent {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (Y : ClosedSubspace X) : IsDecent Y.X :=
  sorry

/-- An integral closed subspace `Z ⊂ Y` whose point-set is an irreducible component
of `|Y|`. -/
def IsIrreducibleComponent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) (Z : ClosedSubspace Y.X) : Prop :=
  IsIntegral Z.X ∧ Z.pointsSet ∈ irreducibleComponents (Points Y.X)

/-- Unpacking of `IsIrreducibleComponent`: integrality of `Z` together with `|Z|`
an irreducible component of `|Y|`. -/
theorem isIrreducibleComponent_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) (Z : ClosedSubspace Y.X) :
    IsIrreducibleComponent Y Z ↔
      IsIntegral Z.X ∧ Z.pointsSet ∈ irreducibleComponents (Points Y.X) :=
  sorry

/-- The canonical integral closed subspace of `Y` on a generic point of `|Y|`, given
by the reduced induced structure on the closure of that point. -/
noncomputable def irreducibleComponent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X) :
    ClosedSubspace Y.X :=
  ofIrreducibleClosed (pointsEquivIrreducibleCloseds Y.X η.1)

/-- The canonical closed subspace on a generic point of `|Y|` is an irreducible
component of `Y`. -/
theorem irreducibleComponent_spec {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X) :
    IsIntegral (irreducibleComponent Y η).X ∧
      IsIrreducibleComponent Y (irreducibleComponent Y η) :=
  sorry

/-- The point-set of the canonical irreducible component on `η` is the closure of
`{η}`. -/
theorem pointsSet_irreducibleComponent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X) :
    (irreducibleComponent Y η).pointsSet = closure {η.1} :=
  sorry

/-- The generic point of an integral closed subspace `Z ⊂ Y`, as a point of `|Y|`. -/
noncomputable def genericPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y : ClosedSubspace X} [IsDecent Y.X] (Z : ClosedSubspace Y.X)
    [IsIntegral Z.X] : Points Y.X :=
  (pointsEquivIrreducibleCloseds Y.X).symm Z.irreducibleClosed

/-- `genericPoint Z` is a generic point of the closed subset `|Z| ⊂ |Y|`. -/
theorem isGenericPoint_genericPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y : ClosedSubspace X} [IsDecent Y.X] (Z : ClosedSubspace Y.X)
    [IsIntegral Z.X] : IsGenericPoint (genericPoint Z) Z.pointsSet :=
  sorry

/-- The generic point of an irreducible component of `Y` lies in `genericPoints Y.X`. -/
theorem mem_genericPoints_genericPoint {S : Scheme.{u}} {X : AlgebraicSpace S}
    {Y : ClosedSubspace X} [IsDecent Y.X] (Z : ClosedSubspace Y.X)
    [IsIntegral Z.X] (hZ : IsIrreducibleComponent Y Z) :
    genericPoint Z ∈ genericPoints Y.X :=
  sorry

/-- Irreducible components of `|Y|` correspond to generic points of `|Y|`. -/
noncomputable def irreducibleComponentsEquivGenericPoints {S : Scheme.{u}}
    {X : AlgebraicSpace S} (Y : ClosedSubspace X) [IsDecent Y.X] :
    irreducibleComponents (Points Y.X) ≃ genericPoints Y.X where
  toFun T := ⟨(_root_.genericPoints.ofComponent T).1, sorry⟩
  invFun η := _root_.genericPoints.component ⟨η.1, sorry⟩
  left_inv := sorry
  right_inv := sorry

/-- The equivalence sends an irreducible component of `|Y|` to a generic point whose
closure is that component. -/
theorem irreducibleComponentsEquivGenericPoints_spec {S : Scheme.{u}}
    {X : AlgebraicSpace S} (Y : ClosedSubspace X) [IsDecent Y.X]
    (T : irreducibleComponents (Points Y.X)) :
    closure {(irreducibleComponentsEquivGenericPoints Y T : Points Y.X)} =
      (T : Set (Points Y.X)) :=
  sorry

/-- An integral closed subspace of `Y` with the same point-set as the canonical
irreducible component on `η` admits a unique morphism over `Y` to that component. -/
theorem existsUnique_hom_irreducibleComponent {S : Scheme.{u}} {X : AlgebraicSpace S}
    (Y : ClosedSubspace X) [IsDecent Y.X] (η : genericPoints Y.X)
    (Z' : ClosedSubspace Y.X) [IsIntegral Z'.X]
    (h : Z'.pointsSet = (irreducibleComponent Y η).pointsSet) :
    ∃! g : Z'.X ⟶ (irreducibleComponent Y η).X,
      g ≫ (irreducibleComponent Y η).ι = Z'.ι :=
  sorry

end ClosedSubspace

end AlgebraicGeometry.AlgebraicSpace
