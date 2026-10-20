module

public import ReasLib.CategoryTheory.Sites.Simplicial.SectionsComplex
import StacksCheckRecall

/-!
# Hom cochain complex of `g_{n!} ℤ` on a morphism diagram of sites

Applying `Hom(-, F)` to the simplicial resolution
`n ↦ g_{n!} ℤ` yields a cosimplicial abelian group, an unaugmented cochain
complex, and the extended ℤ-indexed complex with `Hom(ℤ, F)` in degree `-1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]
variable [∀ n, (ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
variable [HasWeakSheafify (topology C J) (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]

/- Lemma 85.8.2: the canonical augmented section complex on the total site. -/
@[stacks 0D77] #check (CategoryTheory.SimplicialSites.globalSectionsExtended C J :
  Sheaf (topology C J) AddCommGrpCat.{w} →
    CochainComplex AddCommGrpCat.{max u w} ℤ)

#check (CategoryTheory.SimplicialSites.globalSectionsComplexFunctor C J :
  Sheaf (topology C J) AddCommGrpCat.{w} ⥤
    CochainComplex AddCommGrpCat.{max u w} ℕ)

#check (CategoryTheory.SimplicialSites.globalSectionsStage_addEquivRestrict C J :
  ∀ (F : Sheaf (topology C J) AddCommGrpCat.{w}) (n : SimplexCategory),
    ((lowerShriekConstant C J).obj (op n) ⟶ F) ≃+
      (constantInteger C J n ⟶ (stageRestrict C J AddCommGrpCat.{w} n).obj F))

section

variable [HasGlobalSectionsFunctor (topology C J) AddCommGrpCat.{w}]
variable (F : Sheaf (topology C J) AddCommGrpCat.{w})

#check (CategoryTheory.Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
    (topology C J) F :
  (Sheaf.Γ (topology C J) AddCommGrpCat.{w}).obj F ≃+
    (constantIntegerSheaf (topology C J) ⟶ F))

end

section

variable (n : SimplexCategory)
variable [HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor (J n).toGrothendieck AddCommGrpCat.{w}]
variable (F : Sheaf (topology C J) AddCommGrpCat.{w})

#check (CategoryTheory.Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
    (J n).toGrothendieck
    ((stageRestrict C J AddCommGrpCat.{w} n).obj F) :
  (Sheaf.Γ (J n).toGrothendieck AddCommGrpCat.{w}).obj
      ((stageRestrict C J AddCommGrpCat.{w} n).obj F) ≃+
    (constantInteger C J n ⟶ (stageRestrict C J AddCommGrpCat.{w} n).obj F))

end

end CategoryTheory.SimplicialSites
