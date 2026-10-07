module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
import StacksCheckRecall

/-!
@stack 0166
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

variable (W : MorphismProperty SimplexCategory) [W.IsMultiplicative]
variable (δ_mem : ∀ {n : ℕ} (i : Fin (n + 2)), W (SimplexCategory.δ i))
variable (σ_mem : ∀ {n : ℕ} (i : Fin (n + 1)), W (SimplexCategory.σ i))

/- Lemma 14.2.2: every morphism in the simplex category is generated under composition by the
coface and codegeneracy maps. -/
@[stacks 0166 "Lemma 14.2.2"]
#check (SimplexCategory.morphismProperty_eq_top W δ_mem σ_mem : W = ⊤)
