/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sober
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Generic points and the schematic locus of algebraic spaces

On a decent algebraic space the canonical topology on `|X|` is sober, so
irreducible components have generic points. With only finitely many
irreducible components those generic points lie in the schematic locus,
where the local rings are ordinary scheme stalks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space has finitely many irreducible components when every
canonical topology on `|X|` has finitely many irreducible components. -/
@[mk_iff]
class HasFiniteIrreducibleComponents {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- Every canonical topology on `|X|` has finitely many irreducible components. -/
  finite_irreducibleComponents :
    ∀ (τ : TopologicalSpace (Points X)),
      IsPointsTopology X τ → (@irreducibleComponents (Points X) τ).Finite

namespace HasFiniteIrreducibleComponents

/-- A space with finitely many irreducible components has finitely many
irreducible components in every canonical topology on `|X|`. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [HasFiniteIrreducibleComponents X]
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ) :
    (@irreducibleComponents (Points X) τ).Finite :=
  sorry

/-- Finiteness of irreducible components in every canonical topology on `|X|`
witnesses `HasFiniteIrreducibleComponents`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ (τ : TopologicalSpace (Points X)),
      IsPointsTopology X τ → (@irreducibleComponents (Points X) τ).Finite) :
    HasFiniteIrreducibleComponents X :=
  sorry

end HasFiniteIrreducibleComponents

/-- A scheme over `S` with finitely many irreducible components, viewed as an
algebraic space, has finitely many irreducible components. -/
instance instHasFiniteIrreducibleComponents_ofOver {S : Scheme.{u}} (U : Over S)
    [Finite (irreducibleComponents U.left)] :
    HasFiniteIrreducibleComponents (ofOver U) :=
  sorry

/-- Every algebraic space admits a canonical topology on its points. -/
theorem exists_isPointsTopology {S : Scheme.{u}} (X : AlgebraicSpace S) :
    ∃ τ : TopologicalSpace (Points X), IsPointsTopology X τ :=
  sorry

/-- A canonical topology on the points of an algebraic space is unique. -/
theorem isPointsTopology_unique {S : Scheme.{u}} {X : AlgebraicSpace S}
    {τ τ' : TopologicalSpace (Points X)}
    (hτ : IsPointsTopology X τ) (hτ' : IsPointsTopology X τ') : τ = τ' :=
  sorry

/-- The generic points of irreducible components of `|X|` computed in a given
topology on the points. -/
def genericPointsIn {S : Scheme.{u}} (X : AlgebraicSpace S)
    (τ : TopologicalSpace (Points X)) : Set (Points X) :=
  @genericPoints (Points X) τ

/-- `genericPointsIn X τ` is the set of generic points of irreducible components
in the topology `τ`. -/
theorem genericPointsIn_eq {S : Scheme.{u}} (X : AlgebraicSpace S)
    (τ : TopologicalSpace (Points X)) :
    genericPointsIn X τ = @genericPoints (Points X) τ :=
  sorry

/-- The set of generic points of irreducible components of `|X|`, independent of
the choice of canonical topology. -/
def genericPoints {S : Scheme.{u}} (X : AlgebraicSpace S) : Set (Points X) :=
  {x | ∀ (τ : TopologicalSpace (Points X)), IsPointsTopology X τ → x ∈ genericPointsIn X τ}

/-- A point is a generic point of an irreducible component of `|X|` if and only
if it is a generic point in every canonical topology. -/
theorem mem_genericPoints_iff {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} :
    x ∈ genericPoints X ↔
      ∀ (τ : TopologicalSpace (Points X)), IsPointsTopology X τ → x ∈ genericPointsIn X τ :=
  sorry

/-- Relative to any canonical topology, `genericPoints X` agrees with the
topological generic points of `|X|`. -/
theorem genericPoints_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ) :
    genericPoints X = genericPointsIn X τ :=
  sorry

/-- Under a canonical topology, membership in `genericPoints X` is membership in
the topological generic points of `|X|`. -/
theorem mem_genericPoints_iff_of_isPointsTopology {S : Scheme.{u}} {X : AlgebraicSpace S}
    {x : Points X} {τ : TopologicalSpace (Points X)} (hτ : IsPointsTopology X τ) :
    x ∈ genericPoints X ↔ x ∈ genericPointsIn X τ :=
  sorry

/-- Generic points of a scheme over `S` correspond to generic points of the
associated algebraic space. -/
theorem genericPoints_ofOver {S : Scheme.{u}} (U : Over S) :
    genericPoints (ofOver U) = ofOver.pointsEquiv U '' _root_.genericPoints U.left :=
  sorry

/-- The schematic locus of an algebraic space is the set of points that lie in
the image of some open immersion from a scheme over `S`. -/
def schematicLocus {S : Scheme.{u}} (X : AlgebraicSpace S) : Set (Points X) :=
  {x | ∃ (U : Over S) (ι : ofOver U ⟶ X),
    IsOpenImmersion ι ∧ x ∈ Set.range (Points.map ι)}

/-- A point lies in the schematic locus if and only if it is in the image of an
open immersion from a representable algebraic space. -/
theorem mem_schematicLocus_iff {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} :
    x ∈ schematicLocus X ↔
      ∃ (U : Over S) (ι : ofOver U ⟶ X),
        IsOpenImmersion ι ∧ x ∈ Set.range (Points.map ι) :=
  sorry

namespace schematicLocus

/-- The image of an open immersion from a scheme over `S` lands in the schematic
locus. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} {ι : ofOver U ⟶ X}
    [IsOpenImmersion ι] {x : Points X} (hx : x ∈ Set.range (Points.map ι)) :
    x ∈ schematicLocus X :=
  sorry

end schematicLocus

/-- On a decent algebraic space with finitely many irreducible components, every
generic point of an irreducible component lies in the schematic locus. -/
theorem genericPoints_subset_schematicLocus {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsDecent X] [HasFiniteIrreducibleComponents X] :
    genericPoints X ⊆ schematicLocus X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
