module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import stacks_project.Chap85.Lemma_85_27_2_CartesianOver
public import stacks_project.Chap85.Lemma_85_27_2_Datum

/-!
# Lemma 85.27.2

Cartesian simplicial schemes over a fixed simplicial scheme `X` are equivalent to
pairs `(V, φ)` consisting of a scheme over `X _⦋0⦌` and an isomorphism over `X _⦋1⦌`
between the two face pullbacks, satisfying the degeneracy identity and the
`X _⦋2⦌` cocycle.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Simplicial
open CategoryTheory.SimplicialObject

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Lemma 85.27.2: let `X` be a simplicial scheme. The category of simplicial schemes
cartesian over `X` is equivalent to the category of pairs `(V, φ)` where `V` is a scheme
over `X _⦋0⦌` and `φ : (Over.pullback (X.δ 1)).obj V ≅ (Over.pullback (X.δ 0)).obj V` is
an isomorphism over `X _⦋1⦌` such that `(X.σ 0)*φ = 𝟙 V` and
`(X.δ 1)*φ = (X.δ 0)*φ ∘ (X.δ 2)*φ` as morphisms of schemes over `X _⦋2⦌`. -/
@[stacks 07TC]
def cartesianOverEquivalence (X : SimplicialObject Scheme.{u}) :
    CartesianOver X ≌ CartesianDatum X :=
  CategoryTheory.Equivalence.mk CartesianDatum.toDatum CartesianDatum.ofDatum
    CartesianDatum.unitIso CartesianDatum.counitIso

/-- The forward functor of `cartesianOverEquivalence X` extracts the pair `(Y _⦋0⦌, φ)`. -/
theorem cartesianOverEquivalence_functor (X : SimplicialObject Scheme.{u}) :
    (cartesianOverEquivalence X).functor = CartesianDatum.toDatum := sorry

/-- The inverse functor of `cartesianOverEquivalence X` reconstructs `Y_n = X_n ×_{X(τ^n_n)} V`. -/
theorem cartesianOverEquivalence_inverse (X : SimplicialObject Scheme.{u}) :
    (cartesianOverEquivalence X).inverse = CartesianDatum.ofDatum := sorry

/-- On objects, the forward functor of `cartesianOverEquivalence X` has underlying scheme
`Y _⦋0⦌` over `X _⦋0⦌`. -/
theorem cartesianOverEquivalence_functor_obj_schemeOver
    {X : SimplicialObject Scheme.{u}} (Y : CartesianOver X) :
    ((cartesianOverEquivalence X).functor.obj Y).schemeOver =
      Over.mk (Y.obj.hom.app (op ⦋0⦌)) := sorry

end AlgebraicGeometry
