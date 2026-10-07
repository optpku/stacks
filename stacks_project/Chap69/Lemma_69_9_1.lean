module

public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_18_12_Pushforward

/-!
# Injectivity of sections with support along a closed immersion

For a closed immersion of algebraic spaces, the functor of sections with
support in the closed subspace sends injective abelian sheaves on the small
étale site of `X` to injective abelian sheaves on the small étale site of `Z`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.9.1: let `S` be a scheme. Let `i : Z ⟶ X` be a closed immersion of algebraic
spaces over `S`. Let `ℐ` be an injective abelian sheaf on `X_étale`. Then `ℋ_Z(ℐ)` is an
injective abelian sheaf on `Z_étale`. -/
@[stacks 0A4M]
theorem sectionsWithSupport_injective
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (sectionsWithSupport :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjunction : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupport)
    (ℐ : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) [Injective ℐ] :
    Injective (sectionsWithSupport.obj ℐ) :=
  sorry

/-- The functor of sections with support in a closed immersion of algebraic spaces preserves
injective objects on the small étale site. -/
theorem sectionsWithSupport_preservesInjectiveObjects
    {S : Scheme.{u}} {X Z : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i]
    (sectionsWithSupport :
      Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤
        Sheaf (smallEtaleTopology Z) AddCommGrpCat.{u + 1})
    (adjunction : sheafPushforward AddCommGrpCat.{u + 1} i ⊣ sectionsWithSupport) :
    sectionsWithSupport.PreservesInjectiveObjects :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
