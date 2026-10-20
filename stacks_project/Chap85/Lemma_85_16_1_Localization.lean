module

public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.Composition
public import stacks_project.Chap85.Lemma_85_15_2_Localization
public import stacks_project.Chap85.Lemma_85_15_3_Comparison
public import stacks_project.Chap85.Lemma_85_3_2_Total
public import stacks_project.Chap85.Situation_85_3_3_Fiberwise
public import ReasLib.CategoryTheory.Sites.Family.Simplicial.Augmentation

/-!
# Localization functors of a simplicial semi-representable object

The simplicial localization diagram and its stage and total localization
functors remain available through this chapter import.
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

/- The localization categories form the simplicial diagram associated to a family. -/
#check (CategoryTheory.SemiRepresentableFamily.overSiteDiagram :
  SimplicialObject (FormalCoproduct.{w} C) → SimplicialObject Cat.{max u v w, max u v w})

/- Identity-degree localization covers generate the total topology. -/
#check (CategoryTheory.SemiRepresentableFamily.overSiteTotalTopology :
  ∀ (_ : GrothendieckTopology C) (K : SimplicialObject (FormalCoproduct.{w} C)),
    GrothendieckTopology (Grothendieck (overSiteDiagram K)))

/- The total localization functor sends each object to its underlying ambient object. -/
#check (CategoryTheory.SemiRepresentableFamily.totalForget :
  ∀ K : SimplicialObject (FormalCoproduct.{w} C), Grothendieck (overSiteDiagram K) ⥤ C)

/- The stage augmentation composite is localization through degree zero. -/
#check (CategoryTheory.SemiRepresentableFamily.stageForget :
  ∀ (K : SimplicialObject (FormalCoproduct.{w} C)) (n : SimplexCategory),
    OverSite (K.obj (op n)) ⥤ C)

/- The total augmentation functor has the prescribed stage object action. -/
#check (CategoryTheory.SemiRepresentableFamily.augmentationTotalForget :
  ∀ K : SimplicialObject (FormalCoproduct.{w} C), Grothendieck (overSiteDiagram K) ⥤ C)

end CategoryTheory.SemiRepresentableFamily
