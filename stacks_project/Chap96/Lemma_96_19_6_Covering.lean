/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.GerbeMorphism
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology

/-!
# Coverings by the essential image of a 1-morphism

On the associated `τ`-site of a category fibred in groupoids, a 1-morphism
covers by essential image when every object admits a covering family whose
members are isomorphic to images of objects of the source.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

/-- A 1-morphism `f : 𝒰 ⟶ 𝒳` covers by essential image in the associated
`τ`-topology when every object of `𝒳` admits a covering `{xᵢ ⟶ x}` in `𝒳_τ`
whose members are isomorphic to `f(uᵢ)` for objects `uᵢ` of `𝒰`. -/
def coversByEssentialImage (f : U ⟶ X) (τ : StandardTopology) : Prop :=
  ∀ x : X.total,
    ∃ (ι : Type (u + 1)) (Y : ι → X.total) (π : ∀ i, Y i ⟶ x),
      Sieve.generate (Presieve.ofArrows Y π) ∈ X.associatedTopology τ x ∧
        ∀ i, ∃ u : U.total, Nonempty (Y i ≅ (toFunctor f).obj u)

/-- Unfolding of `coversByEssentialImage`. -/
theorem coversByEssentialImage_iff (f : U ⟶ X) (τ : StandardTopology) :
    coversByEssentialImage f τ ↔
      ∀ x : X.total,
        ∃ (ι : Type (u + 1)) (Y : ι → X.total) (π : ∀ i, Y i ⟶ x),
          Sieve.generate (Presieve.ofArrows Y π) ∈ X.associatedTopology τ x ∧
            ∀ i, ∃ u : U.total, Nonempty (Y i ≅ (toFunctor f).obj u) :=
  sorry

/-- Covering by essential image in `𝒳_τ` is equivalent to local essential
surjectivity of `f` on the big `τ`-site of `S`. -/
theorem coversByEssentialImage_iff_locallyEssentiallySurjective
    (f : U ⟶ X) (τ : StandardTopology) :
    coversByEssentialImage f τ ↔
      Hom.LocallyEssentiallySurjective (τ.overTopology S) f :=
  sorry

end AlgebraicGeometry.GroupoidsOver
