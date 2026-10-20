module

public import ReasLib.CategoryTheory.Sites.Grothendieck.SectionsComplex
import StacksCheckRecall

/-!
# Hom cochain complex of `g_{n!} ℤ` on a fiberwise simplicial site

Applying `Hom(-, G)` to the simplicial resolution
`n ↦ g_{n!} ℤ` on the total Grothendieck construction yields a cosimplicial
abelian group, an unaugmented cochain complex, and the extended ℤ-indexed complex with
`Hom(ℤ, G)` in degree `-1`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor AlgebraicTopology
open HomologicalComplex
open scoped Simplicial

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]
variable [∀ n, (ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, (ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, ∀ P : (F.obj n)ᵒᵖ ⥤ Type w, (ι F n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/- Lemma 85.8.2: the canonical augmented section complex on the total site. -/
@[stacks 0D77] #check (CategoryTheory.Grothendieck.fiberSectionsExtended F J :
  Sheaf (topology F J) AddCommGrpCat.{w} →
    CochainComplex AddCommGrpCat.{max u w} ℤ)

#check (CategoryTheory.Grothendieck.fiberSectionsComplexFunctor F J :
  Sheaf (topology F J) AddCommGrpCat.{w} ⥤
    CochainComplex AddCommGrpCat.{max u w} ℕ)

#check (CategoryTheory.Grothendieck.fiberSectionsStage_addEquivRestrict F J :
  ∀ (G : Sheaf (topology F J) AddCommGrpCat.{w}) (n : SimplexCategory),
    ((fiberLowerShriekConstant F J).obj (op n) ⟶ G) ≃+
      (fiberConstantInteger F J n ⟶ (fiberRestrict F J AddCommGrpCat.{w} n).obj G))

section

variable [HasGlobalSectionsFunctor (topology F J) AddCommGrpCat.{w}]
variable (G : Sheaf (topology F J) AddCommGrpCat.{w})

#check (CategoryTheory.Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
    (topology F J) G :
  (Sheaf.Γ (topology F J) AddCommGrpCat.{w}).obj G ≃+
    (constantIntegerSheaf (topology F J) ⟶ G))

end

section

variable (n : SimplexCategory)
variable [HasSheafify (J (op n)).toGrothendieck AddCommGrpCat.{w}]
variable [HasGlobalSectionsFunctor (J (op n)).toGrothendieck AddCommGrpCat.{w}]
variable (G : Sheaf (topology F J) AddCommGrpCat.{w})

#check (CategoryTheory.Sheaf.globalSectionsAddEquivConstantIntegerSheafHomOnSite
    (J (op n)).toGrothendieck
    ((fiberRestrict F J AddCommGrpCat.{w} n).obj G) :
  (Sheaf.Γ (J (op n)).toGrothendieck AddCommGrpCat.{w}).obj
      ((fiberRestrict F J AddCommGrpCat.{w} n).obj G) ≃+
    (fiberConstantInteger F J n ⟶ (fiberRestrict F J AddCommGrpCat.{w} n).obj G))

end

end CategoryTheory.Grothendieck
