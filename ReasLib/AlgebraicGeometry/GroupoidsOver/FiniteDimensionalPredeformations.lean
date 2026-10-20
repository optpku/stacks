module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Projection
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Unpointed
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.DualNumber

/-!
# Finite-dimensional tangent and infinitesimal automorphism spaces

A category fibred in groupoids over a locally
Noetherian scheme has finite-dimensional tangent and infinitesimal automorphism
spaces at every finite-type residue object.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ArtinianLocalAlgCat
open AlgebraicGeometry.GroupoidsOver.Predeformation

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- For every finite-type field `k` over `S` and every object `x0` of
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
locally Noetherian base has finite-dimensional predeformation spaces. -/
instance slice {S : Scheme.{u}} [IsLocallyNoetherian S] (V : Over S)
    [LocallyOfFiniteType V.hom] :
    HasFiniteDimensionalPredeformations (GroupoidsOver.slice V) :=
  sorry

/-- Finite-dimensional predeformations give finite-dimensionality of both the canonical tangent space
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

/-- Finite-dimensional predeformations are equivalent to finite-dimensionality of both the canonical
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

/-- Finite-dimensional predeformations imply that the canonical tangent space of `ℱ_{X, k, x0}` is
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

/-- Finite-dimensional predeformations imply that the canonical space `Inf(ℱ_{X, k, x0})` is
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
