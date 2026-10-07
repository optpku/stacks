module

public import stacks_project.Chap67.Definition_67_47_3_RationalMap

/-!
# Domain of definition of rational maps of algebraic spaces

A rational map is defined at a point of `|X|` when some representative
partial map contains that point in its domain. The domain of definition
is the set of all such points.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace PartialMap

/-- The set of points of `|X|` lying in the domain of a partial map. -/
def points {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : PartialMap X Y) :
    Set (Points X) :=
  Set.range (Points.map f.domain.hom)

/-- Membership in the point-set of a partial map is being the image of a point
of the domain under the structure morphism. -/
theorem mem_points_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {f : PartialMap X Y} {x : Points X} :
    x ∈ f.points ↔ ∃ u : Points f.domain.left, Points.map f.domain.hom u = x :=
  sorry

end PartialMap

namespace RationalMap

/-- The domain of definition of a rational map: the set of points of `|X|` at
which some representative is defined. -/
def domain {S : Scheme.{u}} {X Y : AlgebraicSpace S} (φ : RationalMap X Y) :
    Set (Points X) :=
  {x | ∃ g : PartialMap X Y, x ∈ g.points ∧ g.toRationalMap = φ}

/-- A rational map is defined at a point if that point lies in its domain of
definition. -/
abbrev definedAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (φ : RationalMap X Y) (x : Points X) : Prop :=
  x ∈ φ.domain

/-- A point lies in the domain of a rational map if and only if some
representative contains that point in its domain. -/
theorem mem_domain {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {φ : RationalMap X Y} {x : Points X} :
    x ∈ φ.domain ↔ ∃ g : PartialMap X Y, x ∈ g.points ∧ g.toRationalMap = φ :=
  sorry

/-- A rational map is defined at a point if and only if some representative
contains that point in its domain. -/
theorem definedAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {φ : RationalMap X Y} {x : Points X} :
    φ.definedAt x ↔ ∃ g : PartialMap X Y, x ∈ g.points ∧ g.toRationalMap = φ :=
  sorry

end RationalMap

namespace PartialMap

/-- The points of a partial map lie in the domain of definition of the associated
rational map. -/
theorem points_subset_domain {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (g : PartialMap X Y) : g.points ⊆ g.toRationalMap.domain :=
  sorry

end PartialMap

end AlgebraicGeometry.AlgebraicSpace
