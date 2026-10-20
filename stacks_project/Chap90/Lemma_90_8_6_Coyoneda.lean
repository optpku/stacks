module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Prorepresentable

/-!
# Induced maps of restricted coyoneda functors

A morphism `f : R ⟶ S` in `CompleteLocalAlgCat Λ k` induces a natural transformation
`restrictedCoyoneda S ⟶ restrictedCoyoneda R` by precomposition, restricted along
the inclusion of `ArtinianLocalAlgCat`.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat

#check (CompleteLocalAlgCat.restrictedCoyonedaMap :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S),
    restrictedCoyoneda S ⟶ restrictedCoyoneda R)

#check (CompleteLocalAlgCat.restrictedCoyonedaMap_app :
  ∀ {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (A : ArtinianLocalAlgCat Λ k) (g : S ⟶ ArtinianLocalAlgCat.inclusion.obj A),
    (restrictedCoyonedaMap f).app A g = f ≫ g)

#check (CompleteLocalAlgCat.restrictedCoyonedaMap_id :
  ∀ (R : CompleteLocalAlgCat Λ k),
    restrictedCoyonedaMap (𝟙 R) = 𝟙 (restrictedCoyoneda R))

#check (CompleteLocalAlgCat.restrictedCoyonedaMap_comp :
  ∀ {R S T : CompleteLocalAlgCat Λ k} (f : R ⟶ S) (g : S ⟶ T),
    restrictedCoyonedaMap (f ≫ g) = restrictedCoyonedaMap g ≫ restrictedCoyonedaMap f)

end CompleteLocalAlgCat
