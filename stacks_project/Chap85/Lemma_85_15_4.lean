module

public import ReasLib.CategoryTheory.Sites.Family.Localization.Injective
import StacksCheckRecall

/-!
# Lemma 85.15.4

Localization inverse image along `forget K` preserves injective abelian sheaves
and K-injective complexes of abelian sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe w u v

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/- Lemma 85.15.4 (1): for `K` in `SR(C)`, inverse image along
`forget K : OverSite K ⥤ C` sends injective abelian sheaves to injective abelian sheaves. -/
@[stacks 0D88] #check (CategoryTheory.SemiRepresentableFamily.forget_preservesInjectiveObjects :
  ∀ (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C),
    ((forget K).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
      (overTopology J K) J).PreservesInjectiveObjects)

/- Lemma 85.15.4 (2): for `K` in `SR(C)`, inverse image along
`forget K : OverSite K ⥤ C` sends K-injective complexes of abelian sheaves to
K-injective complexes of abelian sheaves. -/
@[stacks 0D88] #check (CategoryTheory.SemiRepresentableFamily.forget_isKInjective :
  ∀ (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C)
    [HasSheafify J AddCommGrpCat.{max w u v}]
    [HasSheafify (overTopology J K) AddCommGrpCat.{max w u v}]
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max w u v}) ℤ) [I.IsKInjective],
    CochainComplex.IsKInjective
      ((((forget K).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
          (overTopology J K) J).mapHomologicalComplex (up ℤ)).obj I))

end CategoryTheory.SemiRepresentableFamily
