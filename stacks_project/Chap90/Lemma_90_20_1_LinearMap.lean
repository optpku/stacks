module

public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Unpointed
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.ExactSequence

/-!
# Infinitesimal linear maps and source compatibility

The unpointed infinitesimal maps and the two-fibre-product sequence are
provided by their mathematical owners.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor BasedCategory
open scoped Bicategory BasedFunctor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.CofiberedCategoryOver.Groupoids

/-- The based-functor view between the projection-functor presentations. -/
abbrev toOfFunctor
    {F G : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
    (φ : F ⟶ G) : BasedCategory.ofFunctor F.p ⥤ᵇ BasedCategory.ofFunctor G.p :=
  toBasedFunctor φ

end CategoryTheory.CofiberedCategoryOver.Groupoids

variable {X Y : Type v} [Category.{w} X] [Category.{w} Y]
variable {p : X ⥤ ArtinianLocalAlgCat Λ k} {q : Y ⥤ ArtinianLocalAlgCat Λ k}
variable [IsPredeformationCategory p] [IsPredeformationCategory q]
variable [HasRimSchlessinger p] [HasRimSchlessinger q]

#check (CategoryTheory.BasedFunctor.mapInfinitesimalAutomorphismsLinearMap :
  (BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q) →
    infinitesimalAutomorphisms p →ₗ[k] infinitesimalAutomorphisms q)
