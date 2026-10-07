module

public import stacks_project.Chap62.Lemma_62_13_2_Comp
import Mathlib.Tactic.CrossRefAttribute

/-!
# Associativity of the fibre-cycle action with composition of families

This file records that the action of families of cycles on fibres is
associative with the composition of such families.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom
namespace CyclesOnFibers

/-- Lemma 62.13.7: Let `(S, δ)` be as in Situation 42.7.1. Let `X ⟶ Y ⟶ Z` be
morphisms of schemes locally of finite type over `S`. Let `α` be a family of
`r`-cycles on fibres of `X / Y`, `β` a family of `s`-cycles on fibres of
`Y / Z`, and `γ ∈ Z_e(Z)`. Then `cap p (f ≫ g) δ (comp g f α β) γ` equals
`cap (g ≫ p) f δ α (cap p g δ β γ)` in `Z_{r+s+e}(X)`. -/
@[stacks 0H6P]
theorem cap_comp {S X Y Z : Scheme.{u}} [UniversallyCatenary S]
    (p : Z ⟶ S) (g : Y ⟶ Z) (f : X ⟶ Y)
    [LocallyOfFiniteType p] [LocallyOfFiniteType g] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] {r s e : ℤ}
    (α : CyclesOnFibers f r) (β : CyclesOnFibers g s)
    (γ : CycleGroup Z (p.relativeDimensionFunction δ) e) :
    CycleGroup.toAlgebraicCycle (((f ≫ g) ≫ p).relativeDimensionFunction δ)
        (r + s + e) (cap p (f ≫ g) δ (comp g f α β) γ) =
      CycleGroup.toAlgebraicCycle ((f ≫ g ≫ p).relativeDimensionFunction δ)
        (r + (s + e)) (cap (g ≫ p) f δ α (cap p g δ β γ)) := sorry

end CyclesOnFibers
end AlgebraicGeometry.Scheme.Hom
