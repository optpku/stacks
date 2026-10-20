module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.TangentSpace

/-! Typed compatibility checks for the tangent-space API. -/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor.IsPredeformationFunctor

#check (tangentSpace :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type v) [IsPredeformationFunctor F], Type v)

#check (tangentSpace_def :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type v) [IsPredeformationFunctor F],
    tangentSpace F = F.obj (ArtinianLocalAlgCat.dualNumber Λ k))

end CategoryTheory.Functor.IsPredeformationFunctor
