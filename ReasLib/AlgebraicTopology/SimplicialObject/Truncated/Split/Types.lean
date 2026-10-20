module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.Split.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphism properties for split truncated simplicial types

This module detects injectivity, surjectivity, and bijectivity degreewise on the distinguished
summands of split truncated simplicial objects in `Type`.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped SimplexCategory.Truncated

universe u

namespace CategoryTheory.SimplicialObject.Truncated.Split.Hom

variable {n : ℕ}

/-- A morphism of split truncated simplicial objects in types that is injective on the
distinguished summands through the degree of `Δ` is injective at `Δ`. -/
@[stacks 017S "injectivity for morphisms of split truncated simplicial objects"]
theorem app_injective {S₁ S₂ : Split (Type u) n} (Φ : S₁ ⟶ S₂)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (hΦ : ∀ m : Fin (n + 1), m.1 ≤ Δ.unop.obj.len → Function.Injective (Φ.f m)) :
    Function.Injective (Φ.F.app Δ) := sorry

/-- Injectivity at `Δ` of a morphism of split truncated simplicial objects is equivalent to
injectivity on all distinguished summands through the degree of `Δ`. -/
@[stacks 017S "injectivity detected on truncated split summands"]
theorem app_injective_iff {S₁ S₂ : Split (Type u) n} (Φ : S₁ ⟶ S₂)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    Function.Injective (Φ.F.app Δ) ↔
      ∀ m : Fin (n + 1), m.1 ≤ Δ.unop.obj.len → Function.Injective (Φ.f m) := sorry

/-- A morphism of split truncated simplicial objects in types that is surjective on the
distinguished summands through the degree of `Δ` is surjective at `Δ`. -/
@[stacks 017S "surjectivity for morphisms of split truncated simplicial objects"]
theorem app_surjective {S₁ S₂ : Split (Type u) n} (Φ : S₁ ⟶ S₂)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (hΦ : ∀ m : Fin (n + 1), m.1 ≤ Δ.unop.obj.len → Function.Surjective (Φ.f m)) :
    Function.Surjective (Φ.F.app Δ) := sorry

/-- Surjectivity at `Δ` of a morphism of split truncated simplicial objects is equivalent to
surjectivity on all distinguished summands through the degree of `Δ`. -/
@[stacks 017S "surjectivity detected on truncated split summands"]
theorem app_surjective_iff {S₁ S₂ : Split (Type u) n} (Φ : S₁ ⟶ S₂)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    Function.Surjective (Φ.F.app Δ) ↔
      ∀ m : Fin (n + 1), m.1 ≤ Δ.unop.obj.len → Function.Surjective (Φ.f m) := sorry

/-- A morphism of split truncated simplicial objects in types that is bijective on the
distinguished summands through the degree of `Δ` is bijective at `Δ`. -/
@[stacks 017S "bijectivity for morphisms of split truncated simplicial objects"]
theorem app_bijective {S₁ S₂ : Split (Type u) n} (Φ : S₁ ⟶ S₂)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ)
    (hΦ : ∀ m : Fin (n + 1), m.1 ≤ Δ.unop.obj.len → Function.Bijective (Φ.f m)) :
    Function.Bijective (Φ.F.app Δ) := sorry

/-- Bijectivity at `Δ` of a morphism of split truncated simplicial objects is equivalent to
bijectivity on all distinguished summands through the degree of `Δ`. -/
@[stacks 017S "bijectivity detected on truncated split summands"]
theorem app_bijective_iff {S₁ S₂ : Split (Type u) n} (Φ : S₁ ⟶ S₂)
    (Δ : (SimplexCategory.Truncated n)ᵒᵖ) :
    Function.Bijective (Φ.F.app Δ) ↔
      ∀ m : Fin (n + 1), m.1 ≤ Δ.unop.obj.len → Function.Bijective (Φ.f m) := sorry

end CategoryTheory.SimplicialObject.Truncated.Split.Hom
