module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable

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

/-- The morphism of restricted coyoneda functors induced by `f : R ⟶ S`, obtained by
whiskering `coyoneda.map f.op` with `ArtinianLocalAlgCat.inclusion`. -/
noncomputable def restrictedCoyonedaMap {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S) :
    restrictedCoyoneda S ⟶ restrictedCoyoneda R :=
  ArtinianLocalAlgCat.inclusion.whiskerLeft (coyoneda.map f.op)

/-- The component of `restrictedCoyonedaMap f` at `A` is precomposition with `f`. -/
theorem restrictedCoyonedaMap_app {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (A : ArtinianLocalAlgCat Λ k) (g : S ⟶ ArtinianLocalAlgCat.inclusion.obj A) :
    (restrictedCoyonedaMap f).app A g = f ≫ g :=
  sorry

/-- The restricted coyoneda map of an identity is the identity transformation. -/
theorem restrictedCoyonedaMap_id (R : CompleteLocalAlgCat Λ k) :
    restrictedCoyonedaMap (𝟙 R) = 𝟙 (restrictedCoyoneda R) :=
  sorry

/-- Restricted coyoneda maps reverse composition of morphisms in `CompleteLocalAlgCat`. -/
theorem restrictedCoyonedaMap_comp {R S T : CompleteLocalAlgCat Λ k}
    (f : R ⟶ S) (g : S ⟶ T) :
    restrictedCoyonedaMap (f ≫ g) = restrictedCoyonedaMap g ≫ restrictedCoyonedaMap f :=
  sorry

end CompleteLocalAlgCat
