/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.Basic
import StacksCheckRecall

@[expose] public section

universe t uC vC uF vF

open CategoryTheory Opposite

/- 35.4.14.1: The three comparison isomorphisms `D.iso` represent the base changes
`θ ⊗ δ₂⁰`, `θ ⊗ δ₂²`, and `θ ⊗ δ₂¹`. The theorem `iso_trans` says that
the comparison through `δ₂⁰` followed by the comparison through `δ₂²` equals
the comparison through `δ₂¹`.
-/
@[stacks 08WX] #check
  (CategoryTheory.Pseudofunctor.DescentData.iso_trans :
    ∀ {C : Type uC} [Category.{vC} C]
      {F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{vF, uF}}
      {ι : Type t} {S : C} {X : ι → C} {f : ∀ i, X i ⟶ S}
      (D : F.DescentData f) {Y : C} (q : Y ⟶ S) {i₁ i₂ i₃ : ι}
      (f₁ : Y ⟶ X i₁) (f₂ : Y ⟶ X i₂) (f₃ : Y ⟶ X i₃)
      (hf₁ : f₁ ≫ f i₁ = q) (hf₂ : f₂ ≫ f i₂ = q)
      (hf₃ : f₃ ≫ f i₃ = q),
      D.iso q f₁ f₂ hf₁ hf₂ ≪≫ D.iso q f₂ f₃ hf₂ hf₃ =
        D.iso q f₁ f₃ hf₁ hf₃)
