module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import stacks_project.Chap85.Lemma_85_15_1

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

/-- Lemma 85.15.4 (1): for `K` in `SR(C)`, inverse image along
`forget K : OverSite K ⥤ C` sends injective abelian sheaves to injective abelian sheaves. -/
@[stacks 0D88, instance]
instance forget_preservesInjectiveObjects (J : GrothendieckTopology C)
    (K : FormalCoproduct.{w} C) :
    ((forget K).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
      (overTopology J K) J).PreservesInjectiveObjects :=
  sorry

/-- Inverse image along localization at `K` of an injective abelian sheaf is injective. -/
theorem injective_forget (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C)
    {I : Sheaf J AddCommGrpCat.{max w u v}} (hI : Injective I) :
    Injective (((forget K).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
      (overTopology J K) J).obj I) :=
  sorry

/-- Lemma 85.15.4 (2): for `K` in `SR(C)`, inverse image along
`forget K : OverSite K ⥤ C` sends K-injective complexes of abelian sheaves to
K-injective complexes of abelian sheaves. -/
@[stacks 0D88, instance]
instance forget_isKInjective (J : GrothendieckTopology C) (K : FormalCoproduct.{w} C)
    [HasSheafify J AddCommGrpCat.{max w u v}]
    [HasSheafify (overTopology J K) AddCommGrpCat.{max w u v}]
    (I : CochainComplex (Sheaf J AddCommGrpCat.{max w u v}) ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective
      ((((forget K).sheafPushforwardContinuous AddCommGrpCat.{max w u v}
          (overTopology J K) J).mapHomologicalComplex (up ℤ)).obj I) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
