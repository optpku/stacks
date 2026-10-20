/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.LowerShriek
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import stacks_project.Chap85.Situation_85_3_3_MorphismDiagram

public import ReasLib.CategoryTheory.Sites.Simplicial.Stage

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

#check (CategoryTheory.SimplicialSites.stageRestrict C J :
  ∀ (A : Type (w + 1)) [Category.{w} A] (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)],
    Sheaf (topology C J) A ⥤ Sheaf ((J n).toGrothendieck) A)

#check (CategoryTheory.SimplicialSites.inverseImageIso C J :
  ∀ (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [(ofStage C n).IsCocontinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (J n).toGrothendieck (Type w)]
    [HasWeakSheafify (topology C J) (Type w)]
    [∀ F : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension F],
    (ofStage C n).sheafPullbackCocontinuous (Type w)
        (J n).toGrothendieck (topology C J) ≅
      stageRestrict C J (Type w) n)

#check (CategoryTheory.SimplicialSites.sheafLowerShriek_adjunction C J :
  ∀ (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (topology C J) (Type w)]
    [∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P],
    sheafLowerShriek C J n ⊣ stageRestrict C J (Type w) n)

#check (CategoryTheory.SimplicialSites.abelianLowerShriek_adjunction C J :
  ∀ (n : SimplexCategory)
    [(ofStage C n).IsContinuous (J n).toGrothendieck (topology C J)]
    [HasWeakSheafify (topology C J) AddCommGrpCat.{w}]
    [∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w}, (ofStage C n).op.HasLeftKanExtension P],
    abelianLowerShriek C J n ⊣ stageRestrict C J AddCommGrpCat.{w} n)

end CategoryTheory.SimplicialSites
