module

public import stacks_project.Chap68.Definition_68_3_1_FiberDegree

/-!
# Composition of universally bounded fibres

Universally bounded fibres of a morphism from a scheme to an algebraic space are
preserved under precomposition by a scheme morphism over `S` with universally
bounded fibres.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.3.2: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`V ⟶ U` be a morphism of schemes over `S`, and let `U ⟶ X` be a morphism from
`U` to `X`. If the fibres of `V ⟶ U` and `U ⟶ X` are universally bounded, then
so are the fibres of `V ⟶ X`. -/
@[stacks 03JM]
theorem universallyBoundedFibres_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    {V U : Over S} (φ : V ⟶ U) (f : ofOver U ⟶ X)
    (hφ : Scheme.Hom.universallyBoundedFibres φ.left) (hf : universallyBoundedFibres f) :
    universallyBoundedFibres (ofOverMap φ ≫ f) :=
  sorry

/-- If a scheme morphism over `S` has fibre degrees bounded by `n` and a morphism
from a scheme to an algebraic space has fibre degrees bounded by `m`, then their
composite has fibre degrees bounded by `n * m`. -/
theorem degreesOfFibresBoundedBy_comp {S : Scheme.{u}} {X : AlgebraicSpace S}
    {V U : Over S} (φ : V ⟶ U) (f : ofOver U ⟶ X) {n m : ℕ}
    (hφ : Scheme.Hom.degreesOfFibresBoundedBy φ.left n)
    (hf : degreesOfFibresBoundedBy f m) :
    degreesOfFibresBoundedBy (ofOverMap φ ≫ f) (n * m) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
