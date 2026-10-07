module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap98.Lemma_98_27_12
public import stacks_project.Chap98.Lemma_98_27_13_TangentSpace
public import stacks_project.Chap98.Lemma_98_27_4_Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-dimensional tangent spaces of the contraction functor

In Situation 98.27.1 the tangent spaces of the contraction functor `F` are
finite-dimensional over the finite-type field `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Over

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Lemma 98.27.13: In Situation 98.27.1 the tangent spaces of the functor `F`
are finite-dimensional. For every finite-type field point
`kToS : Spec(k) ⟶ S` and every `x0 ∈ F(Spec(k))`, the tangent space
`TF_{k, x0}` is finite-dimensional over `k`. -/
@[stacks 0GI7, instance]
instance instFiniteDimensional_tangentSpace (σ : ContractionSituation S)
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : σ.functor.obj (op (asLocallyNoetherian (Over.mk kToS)))) :
    FiniteDimensional k (tangentSpace σ.functor openImmersion kToS h_factor x0) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
