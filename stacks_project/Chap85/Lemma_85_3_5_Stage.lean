module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Situation_85_3_3_MorphismDiagram

/-!
# Stage inclusion of a simplicial diagram of sites

The degree-`n` inclusion `ofStage C n : C.obj n ⥤ C_total`, the associated morphism of
topoi `g_n : Sh(C_n) ⟶ Sh(C_total)`, restriction `F ↦ F_n`, and the type-valued and
abelian lower-shriek functors along that inclusion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.MorphismOfTopoiIn

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))

/-- The morphism of topoi `g_n : Sh(C_n) ⟶ Sh(C_total)` associated to the degree-`n`
inclusion `ofStage C n`. -/
def ofStageMorphism (n : SimplexCategory)
    [(ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J)]
    [HasSheafify (J n).toGrothendieck (Type w)]
    [∀ F : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension F] :
    MorphismOfTopoiIn (topology C J) (J n).toGrothendieck :=
  (ofStage C n).morphismOfTopoiInOfCocontinuous (J n).toGrothendieck (topology C J)

/-- Inverse image of `g_n` is the sheafified cocontinuous pullback along `ofStage C n`. -/
theorem ofStageMorphism_inverseImage (n : SimplexCategory)
    [(ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J)]
    [HasSheafify (J n).toGrothendieck (Type w)]
    [∀ F : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension F] :
    (ofStageMorphism C J n)⁻¹ =
      (ofStage C n).sheafPullbackCocontinuous (Type w)
        (J n).toGrothendieck (topology C J) :=
  sorry

/-- Restriction of sheaves along the degree-`n` inclusion, i.e. `F ↦ F_n`. -/
abbrev stageRestrict (A : Type (w + 1)) [Category.{w} A] (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)] :
    Sheaf (topology C J) A ⥤ Sheaf ((J n).toGrothendieck) A :=
  (ofStage C n).sheafPushforwardContinuous A (J n).toGrothendieck (topology C J)

/-- `stageRestrict` is continuous sheaf pushforward along `ofStage C n`. -/
theorem stageRestrict_eq (A : Type (w + 1)) [Category.{w} A] (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)] :
    stageRestrict C J A n =
      (ofStage C n).sheafPushforwardContinuous A (J n).toGrothendieck (topology C J) :=
  sorry

/-- Type-valued lower shriek `g^{Sh}_{n!}` along the degree-`n` inclusion. -/
abbrev sheafLowerShriek (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (topology C J) (Type w)]
    [∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P] :
    Sheaf ((J n).toGrothendieck) (Type w) ⥤ Sheaf (topology C J) (Type w) :=
  (ofStage C n).sheafPullback (Type w) (J n).toGrothendieck (topology C J)

/-- Abelian lower shriek `g_{n!}` along the degree-`n` inclusion. -/
abbrev abelianLowerShriek (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
    [∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w}, (ofStage C n).op.HasLeftKanExtension P] :
    Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w} ⥤
      Sheaf (topology C J) AddCommGrpCat.{w} :=
  (ofStage C n).sheafPullback AddCommGrpCat.{w} (J n).toGrothendieck (topology C J)

/-- The canonical cocontinuous-to-continuous comparison along `ofStage C n`. -/
def inverseImageIso (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [(ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (J n).toGrothendieck (Type w)]
    [HasWeakSheafify (topology C J) (Type w)]
    [∀ F : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension F] :
    (ofStage C n).sheafPullbackCocontinuous (Type w)
        (J n).toGrothendieck (topology C J) ≅
      stageRestrict C J (Type w) n :=
  asIso (Functor.CocontinuousPullback.comparison (ofStage C n)
    (J n).toGrothendieck (topology C J))

/-- `sheafLowerShriek` is sheaf pullback along `ofStage C n`. -/
theorem sheafLowerShriek_eq (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (topology C J) (Type w)]
    [∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P] :
    sheafLowerShriek C J n =
      (ofStage C n).sheafPullback (Type w) (J n).toGrothendieck (topology C J) :=
  sorry

/-- `abelianLowerShriek` is sheaf pullback of abelian sheaves along `ofStage C n`. -/
theorem abelianLowerShriek_eq (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
    [∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w}, (ofStage C n).op.HasLeftKanExtension P] :
    abelianLowerShriek C J n =
      (ofStage C n).sheafPullback AddCommGrpCat.{w} (J n).toGrothendieck (topology C J) :=
  sorry

/-- The forward map of `inverseImageIso` is the canonical cocontinuous-to-continuous
comparison. -/
theorem inverseImageIso_hom (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [(ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (J n).toGrothendieck (Type w)]
    [HasWeakSheafify (topology C J) (Type w)]
    [∀ F : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension F] :
    (inverseImageIso C J n).hom =
      Functor.CocontinuousPullback.comparison (ofStage C n)
        (J n).toGrothendieck (topology C J) :=
  sorry

/-- Type-valued lower shriek is left adjoint to restriction along `ofStage C n`. -/
def sheafLowerShriek_adjunction (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (topology C J) (Type w)]
    [∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P] :
    sheafLowerShriek C J n ⊣ stageRestrict C J (Type w) n :=
  (ofStage C n).sheafAdjunctionContinuous (Type w)
    (J n).toGrothendieck (topology C J)

/-- Abelian lower shriek is left adjoint to restriction along `ofStage C n`. -/
def abelianLowerShriek_adjunction (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
    [∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w}, (ofStage C n).op.HasLeftKanExtension P] :
    abelianLowerShriek C J n ⊣ stageRestrict C J AddCommGrpCat.{w} n :=
  (ofStage C n).sheafAdjunctionContinuous AddCommGrpCat.{w}
    (J n).toGrothendieck (topology C J)

/-- The type-valued adjunction is continuous sheaf adjunction along `ofStage C n`. -/
theorem sheafLowerShriek_adjunction_eq (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (topology C J) (Type w)]
    [∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P] :
    sheafLowerShriek_adjunction C J n =
      (ofStage C n).sheafAdjunctionContinuous (Type w)
        (J n).toGrothendieck (topology C J) :=
  sorry

/-- The abelian adjunction is continuous sheaf adjunction along `ofStage C n`. -/
theorem abelianLowerShriek_adjunction_eq (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
    [∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w}, (ofStage C n).op.HasLeftKanExtension P] :
    abelianLowerShriek_adjunction C J n =
      (ofStage C n).sheafAdjunctionContinuous AddCommGrpCat.{w}
        (J n).toGrothendieck (topology C J) :=
  sorry

end CategoryTheory.SimplicialSites
