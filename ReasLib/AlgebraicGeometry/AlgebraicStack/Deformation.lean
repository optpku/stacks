module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.TangentSpace
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Base

/-!
# Deformation finiteness for locally finite type algebraic stacks
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry ArtinianLocalAlgCat
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

/-- The tangent space at a finite-type field-valued object of an algebraic stack
locally of finite type over a locally Noetherian scheme is finite-dimensional. -/
instance instFiniteDimensional_tangentSpace
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (X : GroupoidsOver S) [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x : X.p.Fiber (Over.mk kToS)) :
    FiniteDimensional k ((Functor.fiberIsoClassFunctor
        (predeformationFunctor X openImmersion kToS h_factor x)).obj
      (dualNumber Λ k)) :=
  sorry

/-- The infinitesimal automorphism space at a finite-type field-valued object of
an algebraic stack locally of finite type over a locally Noetherian scheme is
finite-dimensional. -/
instance instFiniteDimensional_infinitesimalAutomorphisms
    {S : Scheme.{u}} [IsLocallyNoetherian S] {Λ k : Type u}
    [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (X : GroupoidsOver S) [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x : X.p.Fiber (Over.mk kToS)) :
    FiniteDimensional k (Functor.infinitesimalAutomorphisms
      (predeformationFunctor X openImmersion kToS h_factor x)) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
