/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_21_4_Functors
public import stacks_project.Chap90.Lemma_90_27_5
public import stacks_project.Chap90.Remarks_90_5_2_Groupoids
import Mathlib.Tactic.CrossRefAttribute

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

/-- A morphism of quotients `[U/R] ⟶ [U'/R']` over `ArtinianLocalAlgCat Λ k`
arises from a morphism of the presenting groupoids in functors. -/
theorem Hom.exists_of_toQuotientBasedFunctor
    {G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)}
    (φ : BasedCategory.ofFunctor G.forget ⟶ BasedCategory.ofFunctor H.forget) :
    ∃ f : Hom G H, Hom.toQuotientBasedFunctor f = φ := sorry

/-- An equivalence of quotients of minimal smooth prorepresentable groupoids in
functors on `ArtinianLocalAlgCat Λ k` yields an isomorphism of those groupoids. -/
theorem nonempty_iso_of_isEquivalence_between
    (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    [IsSmooth H.s H.t] [IsProrepresentable H] [IsMinimal H]
    (φ : BasedCategory.ofFunctor G.forget ⟶ BasedCategory.ofFunctor H.forget)
    [BasedFunctor.IsEquivalence φ] :
    Nonempty (Iso G H) := sorry

/-- Lemma 90.27.7: let `F` be a category cofibered in groupoids over
`ArtinianLocalAlgCat Λ k`. If there exist presentations of `F` by
minimal smooth prorepresentable groupoids in functors `G` and `H`, then
`G` and `H` are isomorphic. -/
@[stacks 06L3]
theorem nonempty_iso_of_minimalPresentations
    (F : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
      (ArtinianLocalAlgCat Λ k))
    (G H : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G] [IsMinimal G]
    [IsSmooth H.s H.t] [IsProrepresentable H] [IsMinimal H]
    (φ : BasedCategory.ofFunctor G.forget ⥤ᵇ F.toBasedCategory)
    (ψ : BasedCategory.ofFunctor H.forget ⥤ᵇ F.toBasedCategory)
    [BasedFunctor.IsEquivalence φ] [BasedFunctor.IsEquivalence ψ] :
    Nonempty (Iso G H) := sorry

end CategoryTheory.GroupoidInFunctors
