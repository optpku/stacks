module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Projection
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation

universe u

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- 98.3.0.2: the projection `p : ℱ_{𝒳,k,x₀} ⥤ ArtinianLocalAlgCat Λ k`
sends each residue lift over `Spec(A)` to its Artinian local base algebra `A`. -/
@[stacks 07T4] #check (AlgebraicGeometry.GroupoidsOver.Predeformation.predeformationFunctor :
  ∀ (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    (x0 : X.p.Fiber (Over.mk kToS)),
    Obj openImmersion kToS h_factor X x0 ⥤ ArtinianLocalAlgCat Λ k)
