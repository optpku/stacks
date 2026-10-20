module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Situation_85_3_3_Fiberwise

public import ReasLib.CategoryTheory.Sites.Grothendieck.LowerShriek

/-!
# Fiber inclusion of a simplicial object of sites

The degree-`n` inclusion `Grothendieck.ι F (op n) : C_n ⥤ C_total` in case B of
Situation 85.3.3, the associated morphism of topoi `g_n`, restriction `F ↦ F_n`,
and the type-valued and abelian lower-shriek functors, together with the
componentwise coproduct/direct-sum formula.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u v w

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))

#check (CategoryTheory.Grothendieck.fiberRestrict F J :
  ∀ (A : Type (w + 1)) [Category.{w} A] (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)],
    Sheaf (topology F J) A ⥤ Sheaf ((J (op n)).toGrothendieck) A)

#check (CategoryTheory.Grothendieck.fiberInverseImageIso F J :
  ∀ (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [(ι F (op n)).IsCocontinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (J (op n)).toGrothendieck (Type w)]
    [HasWeakSheafify (topology F J) (Type w)]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasPointwiseRightKanExtension P],
    (ι F (op n)).sheafPullbackCocontinuous (Type w)
        (J (op n)).toGrothendieck (topology F J) ≅
      fiberRestrict F J (Type w) n)

#check (CategoryTheory.Grothendieck.fiberSheafLowerShriek_adjunction F J :
  ∀ (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (topology F J) (Type w)]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w, (ι F (op n)).op.HasLeftKanExtension P],
    fiberSheafLowerShriek F J n ⊣ fiberRestrict F J (Type w) n)

#check (CategoryTheory.Grothendieck.fiberAbelianLowerShriek_adjunction F J :
  ∀ (n : SimplexCategory)
    [(ι F (op n)).IsContinuous (J (op n)).toGrothendieck (topology F J)]
    [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
    [∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}, (ι F (op n)).op.HasLeftKanExtension P],
    fiberAbelianLowerShriek F J n ⊣ fiberRestrict F J AddCommGrpCat.{w} n)

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

#check (CategoryTheory.Grothendieck.fiberSheafLowerShriek_component F J :
  ∀ {n m : SimplexCategory} (φ : n ⟶ m)
    (G : Sheaf ((J (op n)).toGrothendieck) (Type w)),
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous (Type w)
      (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G ⟶
      (fiberRestrict F J (Type w) m).obj ((fiberSheafLowerShriek F J n).obj G))

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [HasWeakSheafify (topology F J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

#check (CategoryTheory.Grothendieck.fiberAbelianLowerShriek_component F J :
  ∀ {n m : SimplexCategory} (φ : n ⟶ m)
    (G : Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor.sheafPullbackCocontinuous AddCommGrpCat.{w}
      (J (op m)).toGrothendieck (J (op n)).toGrothendieck).obj G ⟶
      (fiberRestrict F J AddCommGrpCat.{w} m).obj
        ((fiberAbelianLowerShriek F J n).obj G))

end CategoryTheory.Grothendieck
