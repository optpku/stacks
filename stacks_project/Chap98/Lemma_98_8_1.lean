module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.TangentSpace
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry ArtinianLocalAlgCat
open AlgebraicGeometry.GroupoidsOver.Predeformation
open scoped Bicategory

noncomputable section

universe u

/- Lemma 98.8.1: for an algebraic stack over a locally Noetherian scheme admitting
a smooth surjective atlas locally of finite type over the base, the tangent space
and the infinitesimal automorphism space of its predeformation category at any
finite-type field-valued object are finite-dimensional over the residue field. -/
@[stacks 07X1]
#check (AlgebraicGeometry.GroupoidsOver.Predeformation.finiteDimensional_tangentSpace :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (X : GroupoidsOver S) [AlgebraicStack X] (x0 : X.p.Fiber (Over.mk kToS))
    (U : Over S) [LocallyOfFiniteType U.hom]
    (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    [Groupoids.Hom.Surjective f],
    FiniteDimensional k ((Functor.fiberIsoClassFunctor
        (predeformationFunctor X openImmersion kToS h_factor x0)).obj
      (dualNumber Λ k)))

#check (AlgebraicGeometry.GroupoidsOver.Predeformation.finiteDimensional_infinitesimalAutomorphisms :
    ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (X : GroupoidsOver S) [AlgebraicStack X] (x0 : X.p.Fiber (Over.mk kToS))
    (U : Over S) [LocallyOfFiniteType U.hom]
    (f : GroupoidsOver.slice U ⟶ X) [Groupoids.Hom.Smooth f]
    [Groupoids.Hom.Surjective f],
    FiniteDimensional k (Functor.infinitesimalAutomorphisms
      (predeformationFunctor X openImmersion kToS h_factor x0)))
