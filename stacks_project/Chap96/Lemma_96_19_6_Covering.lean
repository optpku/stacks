module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Covering

/-!
# Coverings by the essential image of a 1-morphism

This source-facing file preserves the historical covering API for downstream
chapter files while the declarations themselves live in ReasLib.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X : GroupoidsOver S}

#check (coversByEssentialImage : (U ⟶ X) → StandardTopology → Prop)
#check (coversByEssentialImage_iff : ∀ (f : U ⟶ X) (τ : StandardTopology),
  coversByEssentialImage f τ ↔
    ∀ x : X.total,
      ∃ (ι : Type (u + 1)) (Y : ι → X.total) (π : ∀ i, Y i ⟶ x),
        Sieve.generate (Presieve.ofArrows Y π) ∈ X.associatedTopology τ x ∧
          ∀ i, ∃ u : U.total, Nonempty (Y i ≅ (toFunctor f).obj u))
#check (coversByEssentialImage_iff_locallyEssentiallySurjective :
  ∀ (f : U ⟶ X) (τ : StandardTopology),
    coversByEssentialImage f τ ↔
      Hom.LocallyEssentiallySurjective (τ.overTopology S) f)

end AlgebraicGeometry.GroupoidsOver
