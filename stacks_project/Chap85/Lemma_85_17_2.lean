module

public import ReasLib.CategoryTheory.Sites.Family.Simplicial.HomCech
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe w v u

/- Lemma 85.17.2. The unaugmented Čech complex of a hypercovering is canonically
identified with the internal-Hom complex of its free abelian sheaves.
A hypercovering supplies the underlying simplicial formal coproduct used in this
more general comparison. -/
@[stacks 0D8F] #check
  (CategoryTheory.SemiRepresentableFamily.homToCech_isIso :
    ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
      [HasEqualizers C] [HasPullbacks C]
      (K : SimplicialObject (FormalCoproduct.{w} C))
      [HasWeakSheafify J AddCommGrpCat.{max w u v}]
      [∀ n : SimplexCategory,
        ∀ P : (SemiRepresentableFamily.OverSite (K.obj (op n)))ᵒᵖ ⥤
            AddCommGrpCat.{max w u v},
          (SemiRepresentableFamily.forget (K.obj (op n))).op.HasPointwiseRightKanExtension P]
      [∀ {m n : SimplexCategory} (φ : m ⟶ n),
        ∀ P : (SemiRepresentableFamily.OverSite (K.obj (op n)))ᵒᵖ ⥤
            AddCommGrpCat.{max w u v},
          (SemiRepresentableFamily.overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]
      (F : Sheaf J AddCommGrpCat.{max w u v}),
      IsIso (CategoryTheory.SemiRepresentableFamily.homToCech J K F))
