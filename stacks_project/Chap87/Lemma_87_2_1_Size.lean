module

public import Mathlib.SetTheory.Cardinal.Basic
public import Mathlib.Topology.Category.TopCat.Opens
public import stacks_project.Chap87.«87_2_0_2_FormalScheme»

/-!
# Size of a formal scheme

The Stacks size of a formal scheme is `max(ℵ₀, κ₁, κ₂)`, where `κ₁` is the
cardinality of the set of formal affine opens and `κ₂` is the supremum of the
cardinalities of the section rings of those opens.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry
open scoped Cardinal

namespace AlgebraicGeometry.FormalScheme

/-- An open of a formal scheme is a formal affine open if the restricted locally
topologically ringed space is isomorphic to the formal spectrum of an admissible
topological ring. -/
def IsAffineOpen {X : FormalScheme.{u}} (U : Opens X.carrier) : Prop :=
  ∃ (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A),
    Nonempty (X.toLocallyTopologicallyRingedSpace.restrict U.isOpenEmbedding ≅ spf A hA)

/-- The set of formal affine opens of a formal scheme. -/
def affineOpens (X : FormalScheme.{u}) : Set (Opens X.carrier) :=
  {U | IsAffineOpen U}

/-- Membership in `affineOpens` is equivalent to being a formal affine open. -/
theorem mem_affineOpens {X : FormalScheme.{u}} {U : Opens X.carrier} :
    U ∈ X.affineOpens ↔ IsAffineOpen U :=
  sorry

/-- A formal affine open is isomorphic in LTRS to `Spf` of an admissible
topological ring. -/
theorem isAffineOpen_iff {X : FormalScheme.{u}} {U : Opens X.carrier} :
    IsAffineOpen U ↔
      ∃ (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A),
        Nonempty
          (X.toLocallyTopologicallyRingedSpace.restrict U.isOpenEmbedding ≅ spf A hA) :=
  sorry

/-- The Stacks size of a formal scheme,
`ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(X.presheaf.obj (op U))`. -/
noncomputable def size (X : FormalScheme.{u}) : Cardinal.{u} :=
  ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(X.presheaf.obj (op U))

/-- Unfolding of `FormalScheme.size`. -/
theorem size_eq (X : FormalScheme.{u}) :
    X.size = ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(X.presheaf.obj (op U)) :=
  sorry

/-- Countable infinite cardinals are bounded by the Stacks size of any formal
scheme. -/
theorem aleph0_le_size (X : FormalScheme.{u}) : ℵ₀ ≤ X.size :=
  sorry

/-- The set of formal affine opens is bounded in cardinality by the Stacks size. -/
theorem mk_affineOpens_le_size (X : FormalScheme.{u}) : #X.affineOpens ≤ X.size :=
  sorry

/-- Sections over a formal affine open are bounded in cardinality by the Stacks
size. -/
theorem mk_sections_le_size (X : FormalScheme.{u}) (U : X.affineOpens) :
    #(X.presheaf.obj (op U)) ≤ X.size :=
  sorry

end AlgebraicGeometry.FormalScheme
