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

open HasColimitOfHasCoproductsOfHasCoequalizers

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [SmallCategory J]
variable {F : J ⥤ C}
variable {c₁ : Cofan fun f : Σ p : J × J, p.1 ⟶ p.2 ↦ F.obj f.1.1}
variable {c₂ : Cofan F.obj}
variable (s t : c₁.pt ⟶ c₂.pt)
variable
  (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F.map f.2 ≫ c₂.ι.app ⟨f.1.2⟩)
  (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ t = c₂.ι.app ⟨f.1.1⟩)
variable {i : Cofork s t}

/- The source needs the universal property for specified coproduct cocones and a specified
coequalizer. The verified owner `HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit` states
exactly this: `hs` and `ht` identify the arrow-indexed coproduct components, and the resulting
`buildColimit` has the same point as `i`. By contrast, `colimitCoconeOfCoequalizerAndCoproduct` and
`hasColimit_of_coequalizer_and_coproduct` assume all coequalizers, while the tagged theorem
`has_colimits_of_hasCoequalizers_and_coproducts` assumes category-wide coproducts and concludes all
colimits. Recalling `buildIsColimit` introduces no stronger assumptions; its explicit chosen-data
boundary recovers the source statement directly and exposes the induced cocone for downstream use. -/

/- Lemma 4.14.12: for a diagram `F : J ⥤ C`, if one chooses a coproduct of the objects `F.obj j`,
a coproduct of the source objects indexed by morphisms `u : j₁ ⟶ j₂`, and a coequalizer of the two
canonical maps whose `u`-components are the coproduct injection from `F.obj j₁` and the composite of
`F.map u` with the coproduct injection from `F.obj j₂`, then the induced cocone is a colimit cocone
of `F`. This is exactly the canonical mathlib theorem
`HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit`. -/
@[stacks 002P "colimit from the object and arrow-source coproducts and their coequalizer"]
#check
  ((fun (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) (hi : IsColimit i) =>
      buildIsColimit s t hs ht t₁ t₂ hi) :
    ∀ (h₁ : IsColimit c₁) (h₂ : IsColimit c₂) (hi : IsColimit i),
      IsColimit (buildColimit s t hs ht i))

end CategoryTheory.Limits
