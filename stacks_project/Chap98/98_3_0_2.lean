module

public import stacks_project.Chap98.«98_3_0_2_SpecOver»
public import stacks_project.Chap98.«98_3_0_2_Category»
import Mathlib.Tactic.CrossRefAttribute

/-!
# The predeformation functor associated to a residue object

Stacks tag 07T4: the functor `p : ℱ_{𝒳, k, x₀} ⥤ ArtinianLocalAlgCat Λ k`
constructed from a category fibered in groupoids over `Over S` and an object
over a finite-type field-valued point of a locally Noetherian scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- 98.3.0.2: given a locally Noetherian scheme `S`, a category `𝒳` fibered in
groupoids over `Over S`, a finite-type morphism `kToS : Spec(k) ⟶ S`, an open
immersion `openImmersion : Spec(Λ) ⟶ S` through which `kToS` factors by a finite
algebra map `Λ → k`, and an object `x0` of `𝒳` over `Spec(k)`, the functor
`p : ℱ_{𝒳, k, x₀} ⥤ ArtinianLocalAlgCat Λ k` sends a morphism `x₀ ⟶ x` over
`Spec(A)` to the Artinian local `Λ`-algebra `A`. -/
@[stacks 07T4]
def predeformationFunctor
    (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS)) :
    Obj openImmersion kToS h_factor X x0 ⥤ ArtinianLocalAlgCat Λ k :=
  forget openImmersion kToS h_factor X x0

/-- The labeled functor `p` sends an object `x₀ ⟶ x` over `Spec(A)` to `A`. -/
theorem predeformationFunctor_obj
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S)}
    {openImmersion : Spec (CommRingCat.of Λ) ⟶ S} [IsOpenImmersion openImmersion]
    {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    {h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS}
    {x0 : X.p.Fiber (Over.mk kToS)}
    (ξ : Obj openImmersion kToS h_factor X x0) :
    (predeformationFunctor X openImmersion kToS h_factor x0).obj ξ = ξ.base :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
