/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.VectorSpace
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Map.Basic

/-!
# Linear projection from a point of projective space

This file defines the graded map and bundled data underlying projection away from a point of
the projective scheme of a vector space.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.VectorSpace

variable {k : Type u} [Field k]
variable {V : Type u} [AddCommGroup V] [Module k V]

/-- The map of symmetric algebras induced by the inclusion of the kernel of a linear
functional preserves the powers-of-degree-one gradings. -/
theorem projectionGradedMap_mem (q : V →ₗ[k] k) {d : ℕ}
    {x : SymmetricAlgebra k (LinearMap.ker q)}
    (hx : x ∈ grading k (LinearMap.ker q) d) :
    SymmetricAlgebra.lift
        ((SymmetricAlgebra.ι k V).comp (LinearMap.ker q).subtype) x ∈ grading k V d := sorry

/-- The graded symmetric-algebra map induced by the inclusion `ker(q) → V`. -/
def projectionGradedMap (q : V →ₗ[k] k) :
    grading k (LinearMap.ker q) →+*ᵍ grading k V where
  toRingHom :=
    (SymmetricAlgebra.lift
      ((SymmetricAlgebra.ι k V).comp (LinearMap.ker q).subtype)).toRingHom
  map_mem := projectionGradedMap_mem q

/-- Projection from a point of `ℙ(V)`, represented by a surjective linear functional.
Its natural `Proj` domain is required to be precisely the complement of the center. -/
structure LinearProjection (k : Type u) [Field k]
    (V : Type u) [AddCommGroup V] [Module k V] (p : scheme k V) where
  /-- A quotient of `V` onto the line represented by the center. -/
  quotient : V →ₗ[k] k
  /-- The quotient representing the center is onto. -/
  quotient_surjective : Function.Surjective quotient
  /-- The induced rational map is defined exactly away from its center. -/
  domain_eq_compl :
    (projMapDomain (projectionGradedMap quotient) : Set (scheme k V)) = {p}ᶜ

namespace LinearProjection

/-- Construct projection data from a surjective functional representing the center and the
identification of its natural domain with the complement of that center. -/
def mkOfPoint (p : scheme k V) (q : V →ₗ[k] k)
    (hq : Function.Surjective q)
    (hdom : (projMapDomain (projectionGradedMap q) : Set (scheme k V)) = {p}ᶜ) :
    LinearProjection k V p where
  quotient := q
  quotient_surjective := hq
  domain_eq_compl := hdom

/-- The hyperplane `W_p = ker(V → k)` associated to a linear projection. -/
abbrev kernel {p : scheme k V} (r : LinearProjection k V p) : Submodule k V :=
  LinearMap.ker r.quotient

/-- The projective target `ℙ(W_p)` of a linear projection. -/
abbrev target {p : scheme k V} (r : LinearProjection k V p) : Scheme.{u} :=
  scheme k r.kernel

/-- The natural open domain `ℙ(V) \ {p}` of a linear projection. -/
abbrev domain {p : scheme k V} (r : LinearProjection k V p) : (scheme k V).Opens :=
  projMapDomain (projectionGradedMap r.quotient)

/-- The morphism `r_p : ℙ(V) \ {p} ⟶ ℙ(W_p)` induced by the kernel inclusion. -/
def hom {p : scheme k V} (r : LinearProjection k V p) :
    r.domain.toScheme ⟶ r.target :=
  projMapMap (projectionGradedMap r.quotient)

/-- If the center is outside the image of a subscheme, that image lies in the natural domain
of the linear projection. -/
theorem range_subset_domain {p : scheme k V} (r : LinearProjection k V p)
    {X : Scheme.{u}} (i : X ⟶ scheme k V) (hp : p ∉ Set.range i.base) :
    Set.range i.base ⊆ Set.range r.domain.ι := sorry

/-- The restriction of a linear projection to a morphism whose image lies in its domain. -/
def restrict {p : scheme k V} (r : LinearProjection k V p)
    {X : Scheme.{u}} (i : X ⟶ scheme k V)
    (hi : Set.range i.base ⊆ Set.range r.domain.ι) : X ⟶ r.target :=
  IsOpenImmersion.lift r.domain.ι i hi ≫ r.hom

/-- The restricted projection is the ambient projection after the canonical lift through its
open domain. -/
theorem restrict_spec {p : scheme k V} (r : LinearProjection k V p)
    {X : Scheme.{u}} (i : X ⟶ scheme k V)
    (hi : Set.range i.base ⊆ Set.range r.domain.ι) :
    r.restrict i hi = IsOpenImmersion.lift r.domain.ι i hi ≫ r.hom := sorry

end LinearProjection

end AlgebraicGeometry.ProjectiveSpace.VectorSpace
