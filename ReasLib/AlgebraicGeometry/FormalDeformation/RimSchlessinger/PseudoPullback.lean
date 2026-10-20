module

public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Construction

/-!
# Rim-Schlessinger closure under pseudo-pullbacks

The pseudo-pullback of categories satisfying the Rim-Schlessinger condition again
satisfies that condition.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- The pseudo-pullback of a cospan of categories over `ArtinianLocalAlgCat Λ k`
satisfies the Rim-Schlessinger condition when all three categories satisfy it. -/
instance instHasRimSchlessingerPseudoPullback
    {F G H : BasedCategory.{u, u + 1} (ArtinianLocalAlgCat Λ k)}
    (f : H ⥤ᵇ F) (g : G ⥤ᵇ F)
    [HasRimSchlessinger F.p] [HasRimSchlessinger G.p] [HasRimSchlessinger H.p] :
    HasRimSchlessinger (BasedCategory.PseudoPullback f g).p := sorry

end CategoryTheory.Functor
