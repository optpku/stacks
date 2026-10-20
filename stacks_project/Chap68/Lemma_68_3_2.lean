module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiberDegree.Composition
import StacksCheckRecall

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

/- Lemma 68.3.2: Let `S` be a scheme. Let `X` be an algebraic space over `S`. Let
`V ⟶ U` be a morphism of schemes over `S`, and let `U ⟶ X` be a morphism from
`U` to `X`. If the fibres of `V ⟶ U` and `U ⟶ X` are universally bounded, then
so are the fibres of `V ⟶ X`. -/
@[stacks 03JM] #check
  (AlgebraicGeometry.AlgebraicSpace.universallyBoundedFibres_comp :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {V U : Over S}
      (φ : V ⟶ U) (f : ofOver U ⟶ X),
      Scheme.Hom.universallyBoundedFibres φ.left → universallyBoundedFibres f →
        universallyBoundedFibres (ofOverMap φ ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.degreesOfFibresBoundedBy_comp :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {V U : Over S}
    (φ : V ⟶ U) (f : ofOver U ⟶ X) {n m : ℕ},
    Scheme.Hom.degreesOfFibresBoundedBy φ.left n → degreesOfFibresBoundedBy f m →
      degreesOfFibresBoundedBy (ofOverMap φ ≫ f) (n * m))

end AlgebraicGeometry.AlgebraicSpace
