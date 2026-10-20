module

public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct.Over
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits

universe w v u v' u'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (X : C)
variable (K L : FormalCoproduct.{w} (Over X)) (A : Type u') [Category.{v'} A]
variable (f : K ⟶ L)

/- Remark 85.15.5 (Variant for over an object) (1): SR(C, X) is
FormalCoproduct (Over X). A family K in this category has a localization site
whose component topologies are J.over (K.obj i).left. -/
@[stacks 0D89] #check (CategoryTheory.Limits.FormalCoproduct.Over.topology J K :
  GrothendieckTopology (CategoryTheory.Limits.FormalCoproduct.Over.Site K))

/- Remark 85.15.5 (Variant for over an object) (2): sheaves on the family
localization decompose as families of sheaves on the source slice sites C/U_i. -/
@[stacks 0D89] #check (CategoryTheory.Limits.FormalCoproduct.Over.sheafEquiv J K A :
  Sheaf (CategoryTheory.Limits.FormalCoproduct.Over.topology J K) A ≌
    ∀ i : K.I, Sheaf (J.over (K.obj i).left) A)

#check (CategoryTheory.Limits.FormalCoproduct.Over.iteratedSiteEquiv K :
  (Σ i : K.I, Over (K.obj i)) ≌ CategoryTheory.Limits.FormalCoproduct.Over.Site K)

#check (CategoryTheory.Limits.FormalCoproduct.Over.iteratedSite_mem_topology_iff J K :
  ∀ (U : Σ i : K.I, Over (K.obj i))
    (S : Sieve ((CategoryTheory.Limits.FormalCoproduct.Over.iteratedForward K).obj U)),
    S ∈ CategoryTheory.Limits.FormalCoproduct.Over.topology J K
        ((CategoryTheory.Limits.FormalCoproduct.Over.iteratedForward K).obj U) ↔
      S.functorPullback (CategoryTheory.Limits.FormalCoproduct.Over.iteratedForward K) ∈
        CategoryTheory.Sigma.topology (fun i => (J.over X).over (K.obj i)) U)

/- Remark 85.15.5 (Variant for over an object) (3): the localization functor
lands in C/X and composes each arrow to U_i with the given arrow U_i ⟶ X. -/
@[stacks 0D89] #check (CategoryTheory.Limits.FormalCoproduct.Over.localization K :
  CategoryTheory.Limits.FormalCoproduct.Over.Site K ⥤ Over X)

/- Remark 85.15.5 (Variant for over an object) (4): an arrow f : K ⟶ L in
SR(C, X) induces a geometric morphism with left-exact inverse image and its
right-adjoint direct image, using sets in Type (max w u v). -/
@[stacks 0D89] #check (CategoryTheory.Limits.FormalCoproduct.Over.mapAdjunction J f :
  (CategoryTheory.Limits.FormalCoproduct.Over.mapInverseImage J f).obj ⊣
    CategoryTheory.Limits.FormalCoproduct.Over.mapPushforward J f)

#check (CategoryTheory.Limits.FormalCoproduct.Over.mapInverseImage J f :
  Sheaf (CategoryTheory.Limits.FormalCoproduct.Over.topology J L) (Type (max w u v)) ⥤ₗ
    Sheaf (CategoryTheory.Limits.FormalCoproduct.Over.topology J K) (Type (max w u v)))
