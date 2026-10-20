module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.LocallyNoetherian
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A scheme over a field identified with the projective line over that field. -/
structure RationalCurve (k : Type u) [Field k] (X : SchemeOverField k) where
  /-- The projective-line isomorphism over the base field. -/
  iso : X ≅ ProjectiveSpace.schemeOver k 1

/-- Construct a rational-curve witness from a projective-line isomorphism. -/
def RationalCurve.ofIso {k : Type u} [Field k] {X : SchemeOverField k}
    (iso : X ≅ ProjectiveSpace.schemeOver k 1) : RationalCurve k X :=
  { iso := iso }

/-- A rational-curve witness exists exactly when the scheme is isomorphic to the projective line. -/
theorem RationalCurve_iff {k : Type u} [Field k] (X : SchemeOverField k) :
    Nonempty (RationalCurve k X) ↔
      Nonempty (X ≅ ProjectiveSpace.schemeOver k 1) := sorry

/-- The canonical normalization of a reduced irreducible component, over the original field. -/
def RationalCycleWitness.normalizedComponentOver {k : Type u} [Field k]
    (X : SchemeOverField k) [IsNoetherian X.left]
    (component : irreducibleComponents X.left) : SchemeOverField k :=
  Over.mk
    (@Scheme.normalizationToOfIsNoetherian (X.left.irreducibleComponentSubscheme component)
      { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
          (X.left.irreducibleComponentSubschemeι component)
        toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
          (X.left.irreducibleComponentSubschemeι component) } ≫
        X.left.irreducibleComponentSubschemeι component ≫ X.hom)

/-- The canonical map from the normalization of a reduced component to the ambient scheme. -/
def RationalCycleWitness.normalizedComponentTo {k : Type u} [Field k]
    (X : SchemeOverField k) [IsNoetherian X.left]
    (component : irreducibleComponents X.left) :
    (RationalCycleWitness.normalizedComponentOver X component).left ⟶ X.left :=
  @Scheme.normalizationToOfIsNoetherian (X.left.irreducibleComponentSubscheme component)
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (X.left.irreducibleComponentSubschemeι component)
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace
        (X.left.irreducibleComponentSubschemeι component) } ≫
      X.left.irreducibleComponentSubschemeι component

/-- The map from the projective line to the ambient scheme induced by a supplied rational
normalization of an irreducible component. -/
def RationalCycleWitness.projectiveComponentTo {k : Type u} [Field k]
    (X : SchemeOverField k) [IsNoetherian X.left]
    (component : irreducibleComponents X.left)
    (rational : RationalCurve k (RationalCycleWitness.normalizedComponentOver X component)) :
    (ProjectiveSpace.schemeOver k 1).left ⟶ X.left :=
  rational.iso.inv.left ≫ RationalCycleWitness.normalizedComponentTo X component

/-- A projective-line point maps to the ambient scheme by first applying the supplied inverse
rational-normalization isomorphism and then the canonical component map. -/
theorem RationalCycleWitness.projectiveComponentTo_apply {k : Type u} [Field k]
    (X : SchemeOverField k) [IsNoetherian X.left]
    (component : irreducibleComponents X.left)
    (rational : RationalCurve k (RationalCycleWitness.normalizedComponentOver X component))
    (point : ProjectiveSpectrum (ProjectiveSpace.grading k 1)) :
    RationalCycleWitness.projectiveComponentTo X component rational point =
      RationalCycleWitness.normalizedComponentTo X component (rational.iso.inv.left point) :=
  rfl

/-- A reduced nodal cycle with rational component normalizations and exactly two normalization
branches at every edge, including a self-edge in the one-component case. -/
structure RationalCycleWitness (k : Type u) [Field k] (X : SchemeOverField k)
    [noetherian : IsNoetherian X.left] where
  /-- The ambient scheme is reduced. -/
  reduced : IsReduced X.left
  /-- All singular closed points are nodes. -/
  atWorstNodal : SchemeOverField.atWorstNodal X
  /-- The number of components and edges. -/
  n : ℕ
  /-- The cycle is nonempty. -/
  n_pos : 0 < n
  /-- An enumeration of every irreducible component. -/
  components : Fin n ≃ irreducibleComponents X.left
  /-- Each reduced component has projective-line normalization. -/
  rational : ∀ index, RationalCurve k (RationalCycleWitness.normalizedComponentOver X (components index))
  /-- The cyclic successor permutation. -/
  next : Equiv.Perm (Fin n)
  /-- Iterating the successor reaches every component. -/
  next_transitive : ∀ first last, ∃ step : ℕ, step < n ∧ (next^[step]) first = last
  /-- The node on each edge. -/
  node : Fin n → X.left
  /-- Different edges have different nodes. -/
  node_injective : Function.Injective node
  /-- Each edge is a node over the base field. -/
  node_nodal : ∀ index, SchemeOverField.isNode X (node index)
  /-- Every node occurs on a recorded edge. -/
  nodes_exhaustive : ∀ point, SchemeOverField.isNode X point ↔
    ∃ index, node index = point
  /-- The edge node lies on its first component. -/
  node_mem : ∀ index, node index ∈ (components index : Set X.left)
  /-- The edge node lies on its successor component. -/
  node_mem_next : ∀ index, node index ∈ (components (next index) : Set X.left)
  /-- The projective-line coordinate of the normalization branch on the first component. -/
  branchLeft : Fin n → ProjectiveSpectrum (ProjectiveSpace.grading k 1)
  /-- The projective-line coordinate of the normalization branch on the successor component. -/
  branchRight : Fin n → ProjectiveSpectrum (ProjectiveSpace.grading k 1)
  /-- The two branches remain distinct even when both belong to one component. -/
  branches_distinct : ∀ index,
    (index, branchLeft index) ≠ (next index, branchRight index)
  /-- The complete normalization fibre over an edge consists of its two recorded branches. -/
  branch_fiber : ∀ index
    (branch : Fin n × ProjectiveSpectrum (ProjectiveSpace.grading k 1)),
    RationalCycleWitness.projectiveComponentTo X (components branch.1) (rational branch.1)
      branch.2 = node index ↔
      branch = (index, branchLeft index) ∨ branch = (next index, branchRight index)
  /-- Distinct components intersect exactly at their recorded cyclic edges. -/
  component_intersection : ∀ first last, first ≠ last →
    (components first : Set X.left) ∩ (components last : Set X.left) =
      {point | (next first = last ∧ point = node first) ∨
        (next last = first ∧ point = node last)}

/-- Construct a rational cycle from all its component, normalization, node, and branch data. -/
def RationalCycleWitness.ofData {k : Type u} [Field k] {X : SchemeOverField k}
    [noetherian : IsNoetherian X.left]
    (reduced : IsReduced X.left) (atWorstNodal : SchemeOverField.atWorstNodal X)
    (n : ℕ) (n_pos : 0 < n)
    (components : Fin n ≃ irreducibleComponents X.left)
    (rational : ∀ index, RationalCurve k (RationalCycleWitness.normalizedComponentOver X (components index)))
    (next : Equiv.Perm (Fin n))
    (next_transitive : ∀ first last, ∃ step : ℕ, step < n ∧ (next^[step]) first = last)
    (node : Fin n → X.left) (node_injective : Function.Injective node)
    (node_nodal : ∀ index, SchemeOverField.isNode X (node index))
    (nodes_exhaustive : ∀ point, SchemeOverField.isNode X point ↔
      ∃ index, node index = point)
    (node_mem : ∀ index, node index ∈ (components index : Set X.left))
    (node_mem_next : ∀ index, node index ∈ (components (next index) : Set X.left))
    (branchLeft : Fin n → ProjectiveSpectrum (ProjectiveSpace.grading k 1))
    (branchRight : Fin n → ProjectiveSpectrum (ProjectiveSpace.grading k 1))
    (branches_distinct : ∀ index,
      (index, branchLeft index) ≠ (next index, branchRight index))
    (branch_fiber : ∀ index
      (branch : Fin n × ProjectiveSpectrum (ProjectiveSpace.grading k 1)),
      RationalCycleWitness.projectiveComponentTo X (components branch.1) (rational branch.1)
        branch.2 = node index ↔
        branch = (index, branchLeft index) ∨ branch = (next index, branchRight index))
    (component_intersection : ∀ first last, first ≠ last →
      (components first : Set X.left) ∩ (components last : Set X.left) =
        {point | (next first = last ∧ point = node first) ∨
          (next last = first ∧ point = node last)}) : RationalCycleWitness k X :=
  { reduced := reduced
    atWorstNodal := atWorstNodal
    n := n
    n_pos := n_pos
    components := components
    rational := rational
    next := next
    next_transitive := next_transitive
    node := node
    node_injective := node_injective
    node_nodal := node_nodal
    nodes_exhaustive := nodes_exhaustive
    node_mem := node_mem
    node_mem_next := node_mem_next
    branchLeft := branchLeft
    branchRight := branchRight
    branches_distinct := branches_distinct
    branch_fiber := branch_fiber
    component_intersection := component_intersection }

/-- A rational cycle has rational normalizations, all and only its cyclic nodes, and precisely
the two recorded normalization branches at each edge. -/
theorem RationalCycleWitness.spec {k : Type u} [Field k] {X : SchemeOverField k}
    [noetherian : IsNoetherian X.left] (cycle : RationalCycleWitness k X) :
    IsReduced X.left ∧ SchemeOverField.atWorstNodal X ∧ 0 < cycle.n ∧
      (∀ index, Nonempty (RationalCycleWitness.normalizedComponentOver X (cycle.components index) ≅
        ProjectiveSpace.schemeOver k 1)) ∧
      (∀ first last, ∃ step : ℕ,
        step < cycle.n ∧ (cycle.next^[step]) first = last) ∧
      Function.Injective cycle.node ∧
      (∀ index, SchemeOverField.isNode X (cycle.node index)) ∧
      (∀ point, SchemeOverField.isNode X point ↔ ∃ index, cycle.node index = point) ∧
      (∀ index, cycle.node index ∈ (cycle.components index : Set X.left)) ∧
      (∀ index, cycle.node index ∈ (cycle.components (cycle.next index) : Set X.left)) ∧
      (∀ index,
        (index, cycle.branchLeft index) ≠ (cycle.next index, cycle.branchRight index)) ∧
      (∀ index (branch : Fin cycle.n × ProjectiveSpectrum (ProjectiveSpace.grading k 1)),
        RationalCycleWitness.projectiveComponentTo X (cycle.components branch.1)
          (cycle.rational branch.1) branch.2 = cycle.node index ↔
          branch = (index, cycle.branchLeft index) ∨
            branch = (cycle.next index, cycle.branchRight index)) ∧
      (∀ first last, first ≠ last →
        (cycle.components first : Set X.left) ∩ (cycle.components last : Set X.left) =
          {point | (cycle.next first = last ∧ point = cycle.node first) ∨
            (cycle.next last = first ∧ point = cycle.node last)}) :=
  ⟨cycle.reduced, cycle.atWorstNodal, cycle.n_pos,
    (fun index => ⟨(cycle.rational index).iso⟩), cycle.next_transitive,
    cycle.node_injective, cycle.node_nodal, cycle.nodes_exhaustive, cycle.node_mem,
    cycle.node_mem_next, cycle.branches_distinct, cycle.branch_fiber,
    cycle.component_intersection⟩

end AlgebraicGeometry.Scheme.Hom
