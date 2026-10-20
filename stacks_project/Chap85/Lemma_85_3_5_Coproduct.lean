module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import stacks_project.Chap85.Lemma_85_3_5_Stage

public import ReasLib.CategoryTheory.Sites.Simplicial.LowerShriek

/-!
# Componentwise coproduct formula for stage lower shriek

Restriction of `g^{Sh}_{n!} G` (resp. `g_{n!} G`) to the degree-`m` site is the
coproduct (resp. direct sum) of the inverse images `f_φ⁻¹ G` over simplex operators
`φ : n ⟶ m`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor

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

#check (CategoryTheory.SimplicialSites.sheafLowerShriek_component C J :
  ∀ {n m : SimplexCategory} (φ : n ⟶ m)
    (G : Sheaf ((J n).toGrothendieck) (Type w)),
    ((C.map φ).toFunctor.sheafPullback (Type w)
      (J n).toGrothendieck (J m).toGrothendieck).obj G ⟶
      (stageRestrict C J (Type w) m).obj ((sheafLowerShriek C J n).obj G))

#check (CategoryTheory.SimplicialSites.sheafLowerShriek_componentCoproductHom C J :
  ∀ (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m)) (Sheaf ((J m).toGrothendieck) (Type w))]
    (G : Sheaf ((J n).toGrothendieck) (Type w)),
    (∐ fun φ : n ⟶ m =>
      ((C.map φ).toFunctor.sheafPullback (Type w)
        (J n).toGrothendieck (J m).toGrothendieck).obj G) ⟶
      (stageRestrict C J (Type w) m).obj ((sheafLowerShriek C J n).obj G))

variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]

#check (CategoryTheory.SimplicialSites.abelianLowerShriek_component C J :
  ∀ {n m : SimplexCategory} (φ : n ⟶ m)
    (G : Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}),
    ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
      (J n).toGrothendieck (J m).toGrothendieck).obj G ⟶
      (stageRestrict C J AddCommGrpCat.{w} m).obj ((abelianLowerShriek C J n).obj G))

#check (CategoryTheory.SimplicialSites.abelianLowerShriek_componentBiproductHom C J :
  ∀ (n m : SimplexCategory)
    [HasColimitsOfShape (Discrete (n ⟶ m))
      (Sheaf ((J m).toGrothendieck) AddCommGrpCat.{w})]
    (G : Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w}),
    (∐ fun φ : n ⟶ m =>
      ((C.map φ).toFunctor.sheafPullback AddCommGrpCat.{w}
        (J n).toGrothendieck (J m).toGrothendieck).obj G) ⟶
      (stageRestrict C J AddCommGrpCat.{w} m).obj ((abelianLowerShriek C J n).obj G))

end CategoryTheory.SimplicialSites
