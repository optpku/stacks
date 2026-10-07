module

public import stacks_project.Chap85.Lemma_85_17_2_Cech
public import stacks_project.Chap85.Lemma_85_17_2_Hom

/-!
# Lemma 85.17.2

The unaugmented Čech cochain of `a⁻¹ F` along a site-level hypercovering is
canonically identified with `Hom(s(Z_{F(K)^#}), F)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped SemiRepresentableFamily Simplicial

noncomputable section

universe w v u

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasEqualizers C] [HasPullbacks C]
variable (K : HypercoveringOf.Terminal.{w} J)
variable [HasWeakSheafify J AddCommGrpCat.{max w u v}]
variable [HasWeakSheafify J (Type (max w u v))]
variable [J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{max w u v})]
variable [∀ n : SimplexCategory,
    ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (forget (K.simplicial.obj (op n))).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (overMap (K.simplicial.map φ.op)).op.HasPointwiseRightKanExtension P]
variable [∀ {m n : SimplexCategory} (φ : m ⟶ n),
    ∀ P : (OverSite (K.simplicial.obj (op n)))ᵒᵖ ⥤ AddCommGrpCat.{max w u v},
      (overMap (K.simplicial.map φ.op) ⋙
          forget (K.simplicial.obj (op m))).op.HasPointwiseRightKanExtension P]

/-- Lemma 85.17.2: Let `C` be a site with equalizers and fibre products. Let `K` be a
hypercovering. The Čech complex of Lemma 85.9.2 associated to `a⁻¹ F`, namely
`a_{0,*} a_0⁻¹ F ⟶ a_{1,*} a_1⁻¹ F ⟶ a_{2,*} a_2⁻¹ F ⟶ ⋯`, is equal to the complex
`Hom(s(Z_{F(K)^#}), F)`, where `s(Z_{F(K)^#})` is as in Hypercoverings, Definition 25.4.1.
The identification is the canonical comparison morphism `homToCech`. -/
@[stacks 0D8F]
theorem homToCech_isIso (F : Sheaf J AddCommGrpCat.{max w u v}) :
    IsIso (homToCech J K F) :=
  sorry

end CategoryTheory.SemiRepresentableFamily
