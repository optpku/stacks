module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Presentations
import StacksCheckRecall

/-!
# Uniqueness of minimal smooth prorepresentable presentations

Presentations of a category cofibered in groupoids over `C_Λ` by minimal
smooth prorepresentable groupoids in functors are unique up to isomorphism.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

noncomputable section

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/- Lemma 90.27.7: let `F` be a category cofibered in groupoids over
`ArtinianLocalAlgCat Λ k`. If there exist presentations of `F` by
minimal smooth prorepresentable groupoids in functors `G` and `H`, then
`G` and `H` are isomorphic. -/
@[stacks 06L3] #check
  (CategoryTheory.GroupoidInFunctors.nonempty_iso_of_minimalPresentations :
    ∀ (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    [IsSmooth H.s H.t] [IsProrepresentable H] [IsMinimal H]
    (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory)
    (ψ : BasedCategory.ofFunctor H.forget ⥤ᵇ F.toBasedCategory)
    [BasedFunctor.IsEquivalence φ] [BasedFunctor.IsEquivalence ψ],
    Nonempty (Iso G H))

end CategoryTheory.GroupoidInFunctors
