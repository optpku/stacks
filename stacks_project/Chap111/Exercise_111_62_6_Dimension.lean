module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Order.UpperLowerSetTopology
public import Mathlib.Topology.Sober
public import ReasLib.Topology.Sober.Finite
public import ReasLib.Topology.Specialization.Dimension
import Mathlib.Tactic.CrossRefAttribute

/-!
# Five-point specialization diagrams

A labeled configuration of five distinct points with the specializations
`x ⤳ u`, `x ⤳ y`, `y ⤳ z`, `v ⤳ u`, and `v ⤳ z`, together with the
finite Alexandrov model of topological Krull dimension `2`.
-/

@[expose] public section

noncomputable section

universe u

open Topology

namespace FivePointSpecialization

/-- The five labeled vertices of the specialization diagram. -/
inductive Point
  | x
  | y
  | z
  | u
  | v
  deriving DecidableEq

/-- The specialization order on the five-point diagram: the reflexive
transitive closure of `z < y < x`, `u < x`, `u < v`, and `z < v`. -/
def Point.le : Point → Point → Prop
  | .x, .x => True
  | .y, .y | .y, .x => True
  | .z, .z | .z, .y | .z, .x | .z, .v => True
  | .u, .u | .u, .x | .u, .v => True
  | .v, .v => True
  | _, _ => False

/-- Unfolding of `Point.le` as equality or one of the six comparabilities
`z ≤ y`, `z ≤ x`, `z ≤ v`, `y ≤ x`, `u ≤ x`, and `u ≤ v`. -/
theorem Point.le_def {a b : Point} :
    a.le b ↔
      a = b ∨ a = .z ∧ b = .y ∨ a = .z ∧ b = .x ∨ a = .z ∧ b = .v ∨
        a = .y ∧ b = .x ∨ a = .u ∧ b = .x ∨ a = .u ∧ b = .v := sorry

/-- The five-point diagram order is a partial order. -/
instance : PartialOrder Point where
  le := Point.le
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry

/-- `Point.le` is the partial-order relation. -/
theorem Point.le_iff {a b : Point} : a ≤ b ↔ a.le b := sorry

/-- The Hasse and composite comparabilities of the five-point poset. -/
theorem Point.z_le_y : Point.z ≤ Point.y := sorry

/-- `y ≤ x` in the five-point poset. -/
theorem Point.y_le_x : Point.y ≤ Point.x := sorry

/-- `z ≤ x` in the five-point poset. -/
theorem Point.z_le_x : Point.z ≤ Point.x := sorry

/-- `u ≤ x` in the five-point poset. -/
theorem Point.u_le_x : Point.u ≤ Point.x := sorry

/-- `u ≤ v` in the five-point poset. -/
theorem Point.u_le_v : Point.u ≤ Point.v := sorry

/-- `z ≤ v` in the five-point poset. -/
theorem Point.z_le_v : Point.z ≤ Point.v := sorry

/-- `y` and `u` are incomparable, so the longest chain through `x, y, z` has
length `2` rather than passing through `u`. -/
theorem Point.not_y_le_u : ¬ Point.y ≤ Point.u := sorry

/-- `u` and `y` are incomparable. -/
theorem Point.not_u_le_y : ¬ Point.u ≤ Point.y := sorry

/-- `x` and `v` are incomparable. -/
theorem Point.not_x_le_v : ¬ Point.x ≤ Point.v := sorry

/-- `v` and `x` are incomparable. -/
theorem Point.not_v_le_x : ¬ Point.v ≤ Point.x := sorry

/-- `u` and `z` are incomparable, preventing a length-`3` chain through `u`. -/
theorem Point.not_u_le_z : ¬ Point.u ≤ Point.z := sorry

/-- `z` and `u` are incomparable. -/
theorem Point.not_z_le_u : ¬ Point.z ≤ Point.u := sorry

/-- The five-point diagram is a finite type. -/
instance : Fintype Point where
  elems := {.x, .y, .z, .u, .v}
  complete := sorry

/-- The upper-set topology on the five-point poset is finite. -/
instance : Fintype (WithUpperSet Point) := Fintype.ofEquiv Point WithUpperSet.toUpperSet

/-- Distinct points of the five-point Alexandrov space are separable. -/
instance : T0Space (WithUpperSet Point) := sorry

end FivePointSpecialization

/-- A labeled configuration of five distinct points with the specializations
`x ⤳ u`, `x ⤳ y`, `y ⤳ z`, `v ⤳ u`, and `v ⤳ z`. -/
structure FivePointSpecialization (X : Type u) [TopologicalSpace X] where
  /-- The labeling of the five diagram vertices. -/
  point : FivePointSpecialization.Point → X
  /-- The five points are pairwise distinct. -/
  injective : Function.Injective point
  /-- The specialization `x ⤳ u`. -/
  specializes_x_u : point .x ⤳ point .u
  /-- The specialization `x ⤳ y`. -/
  specializes_x_y : point .x ⤳ point .y
  /-- The specialization `y ⤳ z`. -/
  specializes_y_z : point .y ⤳ point .z
  /-- The specialization `v ⤳ u`. -/
  specializes_v_u : point .v ⤳ point .u
  /-- The specialization `v ⤳ z`. -/
  specializes_v_z : point .v ⤳ point .z

namespace FivePointSpecialization

variable {X : Type u} [TopologicalSpace X]

/-- The vertex `x` of a five-point specialization configuration. -/
abbrev x (D : FivePointSpecialization X) : X := D.point .x

/-- The vertex `y` of a five-point specialization configuration. -/
abbrev y (D : FivePointSpecialization X) : X := D.point .y

/-- The vertex `z` of a five-point specialization configuration. -/
abbrev z (D : FivePointSpecialization X) : X := D.point .z

/-- The vertex `u` of a five-point specialization configuration. -/
abbrev u (D : FivePointSpecialization X) : X := D.point .u

/-- The vertex `v` of a five-point specialization configuration. -/
abbrev v (D : FivePointSpecialization X) : X := D.point .v

/-- The standard five-point configuration in the upper-set topology. -/
def standard : FivePointSpecialization (WithUpperSet Point) where
  point := WithUpperSet.toUpperSet
  injective := WithUpperSet.toUpperSet.injective
  specializes_x_u := sorry
  specializes_x_y := sorry
  specializes_y_z := sorry
  specializes_v_u := sorry
  specializes_v_z := sorry

/-- The standard labeling is the identity onto `WithUpperSet Point`. -/
theorem standard_point (p : Point) : standard.point p = WithUpperSet.toUpperSet p := sorry

/-- The defining injectivity and five specializations of a configuration. -/
theorem spec (D : FivePointSpecialization X) :
    Function.Injective D.point ∧ D.x ⤳ D.u ∧ D.x ⤳ D.y ∧ D.y ⤳ D.z ∧
      D.v ⤳ D.u ∧ D.v ⤳ D.z := sorry

/-- Distinct labels are sent to distinct points. -/
theorem point_eq_iff (D : FivePointSpecialization X) {a b : Point} :
    D.point a = D.point b ↔ a = b := sorry

/-- Package an injective labeling together with the five specializations. -/
def ofPoints (point : Point → X) (injective : Function.Injective point)
    (specializes_x_u : point .x ⤳ point .u) (specializes_x_y : point .x ⤳ point .y)
    (specializes_y_z : point .y ⤳ point .z) (specializes_v_u : point .v ⤳ point .u)
    (specializes_v_z : point .v ⤳ point .z) : FivePointSpecialization X where
  point := point
  injective := injective
  specializes_x_u := specializes_x_u
  specializes_x_y := specializes_x_y
  specializes_y_z := specializes_y_z
  specializes_v_u := specializes_v_u
  specializes_v_z := specializes_v_z

/-- `ofPoints` recovers the supplied labeling. -/
theorem ofPoints_point (point : Point → X) (injective : Function.Injective point)
    (specializes_x_u : point .x ⤳ point .u) (specializes_x_y : point .x ⤳ point .y)
    (specializes_y_z : point .y ⤳ point .z) (specializes_v_u : point .v ⤳ point .u)
    (specializes_v_z : point .v ⤳ point .z) :
    (ofPoints point injective specializes_x_u specializes_x_y specializes_y_z
      specializes_v_u specializes_v_z).point = point := sorry

/-- Exercise 111.62.6 (Dimension) (1): every sober space carrying five distinct
points `x`, `y`, `z`, `u`, `v` with specializations `x ⤳ u`, `x ⤳ y`,
`y ⤳ z`, `v ⤳ u`, and `v ⤳ z` has topological Krull dimension at least `2`. -/
@[stacks 0FWQ]
theorem two_le_topologicalKrullDim [QuasiSober X] [T0Space X]
    (D : FivePointSpecialization X) : 2 ≤ topologicalKrullDim X := sorry

/-- Exercise 111.62.6 (Dimension) (2): the upper-set topology on the five-point
poset is a sober space of topological Krull dimension `2` realizing the
diagram. -/
@[stacks 0FWQ]
theorem standard_topologicalKrullDim_eq_two :
    topologicalKrullDim (WithUpperSet Point) = 2 := sorry

/-- Exercise 111.62.6 (Dimension) (3): if the ambient space is the prime
spectrum of a finite-type algebra over a field and `x ⤳ u` is an immediate
specialization, then `v ⤳ z` is not immediate. -/
@[stacks 0FWQ]
theorem not_isImmediateSpecialization {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A]
    (D : FivePointSpecialization (PrimeSpectrum A))
    (h_immediate : IsImmediateSpecialization D.x D.u) :
    ¬ IsImmediateSpecialization D.v D.z := sorry

/-- Under the hypotheses of the algebraic clause, the specialization `v ⤳ z`
has a point strictly between the endpoints. -/
theorem exists_mem_specialization_interval {k A : Type u} [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A]
    (D : FivePointSpecialization (PrimeSpectrum A))
    (h_immediate : IsImmediateSpecialization D.x D.u) :
    ∃ w, D.v ⤳ w ∧ w ⤳ D.z ∧ w ≠ D.v ∧ w ≠ D.z := sorry

end FivePointSpecialization
