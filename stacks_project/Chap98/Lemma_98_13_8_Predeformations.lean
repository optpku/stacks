/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap90.Lemma_90_20_1_LinearMap
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap98.«98_3_0_2»

/-!
# Finite-dimensional tangent and infinitesimal automorphism spaces

Axiom [3] of Section 98.14: a category fibred in groupoids over a locally
Noetherian scheme has finite-dimensional tangent and infinitesimal automorphism
spaces at every finite-type residue object.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ArtinianLocalAlgCat
open AlgebraicGeometry.GroupoidsOver.Predeformation

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Axiom [3]: for every finite-type field `k` over `S` and every object `x0` of
`X` over `Spec(k)`, the canonical tangent space `Tℱ_{X, k, x0}` and the
canonical infinitesimal automorphism space `Inf(ℱ_{X, k, x0})` are
finite-dimensional over `k`. -/
class HasFiniteDimensionalPredeformations {S : Scheme.{u}} [IsLocallyNoetherian S]
    (X : GroupoidsOver S) : Prop where
  /-- The canonical tangent space of every residue-field predeformation functor
  is finite-dimensional. -/
  tangent :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
      [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ S)
      [LocallyOfFiniteType kToS]
      (h_factor :
        Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
      (x0 : X.p.Fiber (Over.mk kToS))
      [Functor.IsPredeformationCategory
        (predeformationFunctor X openImmersion kToS h_factor x0)]
      [Functor.HasSchlessingerH2
        (Functor.fiberIsoClassFunctor
          (predeformationFunctor X openImmersion kToS h_factor x0))],
      FiniteDimensional k
        ((Functor.fiberIsoClassFunctor
            (predeformationFunctor X openImmersion kToS h_factor x0)).obj
          (dualNumber Λ k))
  /-- The canonical infinitesimal automorphism space of every residue-field
  predeformation functor is finite-dimensional. -/
  infinitesimalAut :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
      [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ S)
      [LocallyOfFiniteType kToS]
      (h_factor :
        Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
      (x0 : X.p.Fiber (Over.mk kToS))
      [Functor.IsPredeformationCategory
        (predeformationFunctor X openImmersion kToS h_factor x0)]
      [Functor.HasRimSchlessinger
        (predeformationFunctor X openImmersion kToS h_factor x0)],
      FiniteDimensional k
        (Functor.infinitesimalAutomorphisms
          (predeformationFunctor X openImmersion kToS h_factor x0))

namespace HasFiniteDimensionalPredeformations

/-- The canonical slice fibration of a scheme locally of finite type over a
locally Noetherian base satisfies axiom [3]. -/
instance slice {S : Scheme.{u}} [IsLocallyNoetherian S] (V : Over S)
    [LocallyOfFiniteType V.hom] :
    HasFiniteDimensionalPredeformations (GroupoidsOver.slice V) :=
  sorry

/-- Axiom [3] supplies finite-dimensionality of both the canonical tangent space
and the canonical infinitesimal automorphism space of every residue-field
predeformation functor. -/
theorem spec {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S)
    [HasFiniteDimensionalPredeformations X] :
    (∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
      [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ S)
      [LocallyOfFiniteType kToS]
      (h_factor :
        Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
      (x0 : X.p.Fiber (Over.mk kToS))
      [Functor.IsPredeformationCategory
        (predeformationFunctor X openImmersion kToS h_factor x0)]
      [Functor.HasSchlessingerH2
        (Functor.fiberIsoClassFunctor
          (predeformationFunctor X openImmersion kToS h_factor x0))],
      FiniteDimensional k
        ((Functor.fiberIsoClassFunctor
            (predeformationFunctor X openImmersion kToS h_factor x0)).obj
          (dualNumber Λ k))) ∧
      ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
        [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ S)
        [LocallyOfFiniteType kToS]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
        (x0 : X.p.Fiber (Over.mk kToS))
        [Functor.IsPredeformationCategory
          (predeformationFunctor X openImmersion kToS h_factor x0)]
        [Functor.HasRimSchlessinger
          (predeformationFunctor X openImmersion kToS h_factor x0)],
        FiniteDimensional k
          (Functor.infinitesimalAutomorphisms
            (predeformationFunctor X openImmersion kToS h_factor x0)) :=
  sorry

/-- Axiom [3] is equivalent to finite-dimensionality of both the canonical
spaces `Tℱ_{X, k, x0}` and `Inf(ℱ_{X, k, x0})` at every finite-type residue
object. -/
theorem iff {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S) :
    HasFiniteDimensionalPredeformations X ↔
      (∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
        [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ S)
        [LocallyOfFiniteType kToS]
        (h_factor :
          Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
        (x0 : X.p.Fiber (Over.mk kToS))
        [Functor.IsPredeformationCategory
          (predeformationFunctor X openImmersion kToS h_factor x0)]
        [Functor.HasSchlessingerH2
          (Functor.fiberIsoClassFunctor
            (predeformationFunctor X openImmersion kToS h_factor x0))],
        FiniteDimensional k
          ((Functor.fiberIsoClassFunctor
              (predeformationFunctor X openImmersion kToS h_factor x0)).obj
            (dualNumber Λ k))) ∧
        ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
          [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
          [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ S)
          [LocallyOfFiniteType kToS]
          (h_factor :
            Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
          (x0 : X.p.Fiber (Over.mk kToS))
          [Functor.IsPredeformationCategory
            (predeformationFunctor X openImmersion kToS h_factor x0)]
          [Functor.HasRimSchlessinger
            (predeformationFunctor X openImmersion kToS h_factor x0)],
          FiniteDimensional k
            (Functor.infinitesimalAutomorphisms
              (predeformationFunctor X openImmersion kToS h_factor x0)) :=
  sorry

/-- Axiom [3] implies that the canonical tangent space of `ℱ_{X, k, x0}` is
finite-dimensional. -/
theorem finiteDimensional_tangent {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [HasFiniteDimensionalPredeformations X]
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ S)
    [LocallyOfFiniteType kToS]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS))
    [Functor.IsPredeformationCategory
      (predeformationFunctor X openImmersion kToS h_factor x0)]
    [Functor.HasSchlessingerH2
      (Functor.fiberIsoClassFunctor
        (predeformationFunctor X openImmersion kToS h_factor x0))] :
    FiniteDimensional k
      ((Functor.fiberIsoClassFunctor
          (predeformationFunctor X openImmersion kToS h_factor x0)).obj
        (dualNumber Λ k)) :=
  sorry

/-- Axiom [3] implies that the canonical space `Inf(ℱ_{X, k, x0})` is
finite-dimensional. -/
theorem finiteDimensional_infinitesimalAut {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [HasFiniteDimensionalPredeformations X]
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
    [IsOpenImmersion openImmersion] (kToS : Spec (CommRingCat.of k) ⟶ S)
    [LocallyOfFiniteType kToS]
    (h_factor :
      Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS))
    [Functor.IsPredeformationCategory
      (predeformationFunctor X openImmersion kToS h_factor x0)]
    [Functor.HasRimSchlessinger
      (predeformationFunctor X openImmersion kToS h_factor x0)] :
    FiniteDimensional k
      (Functor.infinitesimalAutomorphisms
        (predeformationFunctor X openImmersion kToS h_factor x0)) :=
  sorry

end HasFiniteDimensionalPredeformations

end AlgebraicGeometry.GroupoidsOver
