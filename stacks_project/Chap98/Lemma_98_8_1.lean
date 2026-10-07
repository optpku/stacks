module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap98.«98_3_0_2»
public import stacks_project.Chap98.Lemma_98_3_1
public import stacks_project.Chap98.Lemma_98_5_2
public import stacks_project.Chap98.Lemma_98_6_1
public import stacks_project.Chap98.Remark_98_6_2
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite-dimensional tangent and infinitesimal automorphism spaces

If `X` is an algebraic stack over a locally Noetherian scheme `S` admitting a
smooth surjective atlas from a scheme locally of finite type over `S`, then for
every predeformation functor `ℱ_{X, k, x0}` of Section 98.3 both `Tℱ` and
`Inf(ℱ)` are finite-dimensional over `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ArtinianLocalAlgCat
open AlgebraicGeometry.GroupoidsOver.Predeformation
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

/-- Lemma 98.8.1 (1): if `S` is locally Noetherian, `X` is an algebraic stack,
`U` is a scheme locally of finite type over `S`, and `(Sch/U)_fppf ⟶ X` is
smooth and surjective, then for any `ℱ = ℱ_{X, k, x0}` as in Section 98.3 the
tangent space `Tℱ` is finite-dimensional over `k`. -/
@[stacks 07X1]
theorem finiteDimensional_tangentSpace
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (X : GroupoidsOver S) [AlgebraicStack X] (x0 : X.p.Fiber (Over.mk kToS))
    (U : Over S) [LocallyOfFiniteType U.hom]
    (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    [Groupoids.Hom.Surjective f] :
    FiniteDimensional k ((Functor.fiberIsoClassFunctor
        (predeformationFunctor X openImmersion kToS h_factor x0)).obj
      (dualNumber Λ k)) :=
  sorry

/-- Lemma 98.8.1 (2): if `S` is locally Noetherian, `X` is an algebraic stack,
`U` is a scheme locally of finite type over `S`, and `(Sch/U)_fppf ⟶ X` is
smooth and surjective, then for any `ℱ = ℱ_{X, k, x0}` as in Section 98.3 the
infinitesimal automorphism space `Inf(ℱ_{X, k, x0})` is finite-dimensional over
`k`. -/
@[stacks 07X1]
theorem finiteDimensional_infinitesimalAutomorphisms
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (X : GroupoidsOver S) [AlgebraicStack X] (x0 : X.p.Fiber (Over.mk kToS))
    (U : Over S) [LocallyOfFiniteType U.hom]
    (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    [Groupoids.Hom.Surjective f] :
    FiniteDimensional k (Functor.infinitesimalAutomorphisms
      (predeformationFunctor X openImmersion kToS h_factor x0)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
