module

public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicStack.RimSchlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Deformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Unpointed
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger

/-!
# Finite-dimensional tangent and infinitesimal automorphism spaces

An algebraic stack with a smooth surjective atlas locally of finite type over a
locally Noetherian base has finite-dimensional tangent and infinitesimal
automorphism spaces at finite-type field-valued objects.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ArtinianLocalAlgCat
open AlgebraicGeometry.GroupoidsOver.Predeformation
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

/-- The tangent space of the predeformation category at a finite-type field-valued
object of an algebraic stack over a locally Noetherian scheme is finite-dimensional
when the stack admits a smooth surjective atlas locally of finite type over the base. -/
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

/-- The infinitesimal automorphism space of the predeformation category at a
finite-type field-valued object of an algebraic stack over a locally Noetherian scheme
is finite-dimensional when the stack admits a smooth surjective atlas locally of
finite type over the base. -/
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
