module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
public import ReasLib.CategoryTheory.Fibered.AdjointFactorization.Inclusion

/-!
# Adjunction and existence API for adjoint factorization

The final leaf states the adjunction carried by the source projection and the
source-facing factorization existence theorem.
-/

@[expose] public section

open CategoryTheory
open scoped Bicategory

universe u v w

namespace CategoryTheory.FiberedCategoryOver

variable {C : Type u} [Category.{v} C]
variable {X Y : FiberedCategoryOver.{u, v, w, w} C}

noncomputable section

namespace AdjointFactorization

/-- The source projection is left adjoint to the identity-arrow inclusion. The result is stated as
`Nonempty` because a bicategorical adjunction contains unit and counit data. -/
theorem nonemptyAdjunction (F : X ⟶ Y) :
    Nonempty (toSource F ⊣ inclusion F) := sorry
/- Proof strategy: at a vertical arrow `y ⟶ F(x)`, use its comparison arrow for the unit and use
the identity comparison at `x` for the counit. Naturality is the comma-square equation, and both
triangle identities reduce componentwise to identity and associativity laws. -/

end AdjointFactorization

/-- Lemma 4.33.14 (Stacks 08NF): every `1`-morphism `F : X ⟶ Y` of fibred categories over `C`
factors as `F = u ≫ v`, where `u` is fully faithful, `w` is left adjoint to `u`, and `v` is
fibred. -/
@[stacks 08NF]
theorem AdjointFactorization.exists (F : X ⟶ Y) :
    ∃ X' : FiberedCategoryOver C, ∃ u : X ⟶ X', ∃ v : X' ⟶ Y, ∃ w : X' ⟶ X,
      ∃ _ : (toFunctor u).FullyFaithful, ∃ _ : w ⊣ u,
        ∃ _ : (toFunctor v).IsFibered, F = u ≫ v := sorry
/- Proof strategy: take `AdjointFactorization.middle F`, `AdjointFactorization.inclusion F`,
`AdjointFactorization.toTarget F`, and `AdjointFactorization.toSource F`; use
`AdjointFactorization.inclusionFullyFaithful F`. The comparison arrows define the unit
and the identity comparisons define the counit of
`AdjointFactorization.toSource F ⊣ AdjointFactorization.inclusion F`; prove both triangle laws
componentwise, equivalently use `AdjointFactorization.nonemptyAdjunction F`. Finish with
`AdjointFactorization.toTargetIsFibered` and
`AdjointFactorization.inclusion_comp_toTarget`. -/

end

end CategoryTheory.FiberedCategoryOver
