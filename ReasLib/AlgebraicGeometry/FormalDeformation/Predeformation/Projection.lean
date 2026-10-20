module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Category
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation

/-!
# The projection from residue lifts to Artinian local algebras
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The projection from residue lifts in a category fibered in groupoids over `Over S`
to their Artinian local base algebras. -/
def predeformationFunctor
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS)) :
    Obj openImmersion kToS h_factor X x0 ⥤ ArtinianLocalAlgCat Λ k :=
  forget openImmersion kToS h_factor X x0

/-- The predeformation projection sends an object `x₀ ⟶ x` over `Spec(A)` to `A`. -/
theorem predeformationFunctor_obj
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}
    {openImmersion : Spec (CommRingCat.of Λ) ⟶ S} [IsOpenImmersion openImmersion]
    {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    {h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS}
    {x0 : X.p.Fiber (Over.mk kToS)}
    (ξ : Obj openImmersion kToS h_factor X x0) :
    (predeformationFunctor X openImmersion kToS h_factor x0).obj ξ = ξ.base :=
  sorry

/-- The projection from residue lifts to Artinian local base algebras is a
predeformation category. -/
instance instIsPredeformationCategory_predeformationFunctor
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS)) :
    CategoryTheory.Functor.IsPredeformationCategory
      (predeformationFunctor X openImmersion kToS h_factor x0) := sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
