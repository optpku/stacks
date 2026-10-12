/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import StacksCheckRecall

@[expose] public section


universe w v u

namespace CategoryTheory.Limits

open HasLimitOfHasProductsOfHasEqualizers

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [SmallCategory J]
variable {F : J ⥤ C}
variable {c₁ : Fan F.obj}
variable {c₂ : Fan fun f : Σ p : J × J, p.1 ⟶ p.2 ↦ F.obj f.1.2}
variable (s t : c₁.pt ⟶ c₂.pt)
variable
  (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
  (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩)
variable {i : Fork s t}

/- The source needs a limit cone built from two particular product cones and one particular
equalizer for a fixed diagram. The verified owner candidates are `buildIsLimit`,
`hasLimit_of_equalizer_and_product`, and `has_limits_of_hasEqualizers_and_products`; the latter two
replace the chosen equalizer by global `HasEqualizers C`, and the last also replaces the chosen
products by global `HasProducts C`. Thus `buildIsLimit` is exact at the cone level: it generalizes
only from the textbook maps `ψ`, `φ` to maps `s`, `t` satisfying their component equations, and the
source is recovered with `s = ψ`, `t = φ`, and `i` their equalizer fork. Recalling this owner keeps
the concrete `buildLimit` cone available for downstream use without a parallel wrapper. -/

/- Lemma 4.14.11: for a diagram `F : J ⥤ C`, if one chooses a product of the objects `F.obj j`,
a product of the target objects indexed by morphisms `u : j₁ ⟶ j₂`, and an equalizer of the two
canonical maps whose `u`-components are the projection to `F.obj j₂` and the composite of the
projection to `F.obj j₁` with `F.map u`, then the induced cone is a limit cone of `F`. This is
exactly the canonical mathlib theorem
`HasLimitOfHasProductsOfHasEqualizers.buildIsLimit`. -/
@[stacks 002N "specific products and equalizer construct a limit cone"]
#check
  ((fun (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) (hi : IsLimit i) =>
      buildIsLimit s t hs ht t₁ t₂ hi) :
    ∀ (h₁ : IsLimit c₁) (h₂ : IsLimit c₂) (hi : IsLimit i),
      IsLimit (buildLimit s t hs ht i))

end CategoryTheory.Limits
