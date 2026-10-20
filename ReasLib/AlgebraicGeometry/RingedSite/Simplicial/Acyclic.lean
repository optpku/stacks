/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.CategoryTheory.Sites.Cohomology.Ext
public import ReasLib.CategoryTheory.Sites.Simplicial.Stage
public import ReasLib.CategoryTheory.Sites.Grothendieck.LowerShriek

/-!
# Total acyclicity of component restrictions of injective modules
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.SimplicialSites

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J]

/-- The restriction to any stage of the underlying abelian sheaf of an injective module
over a ring sheaf on the total site of a simplicial diagram of morphisms of sites is
totally acyclic. -/
@[instance]
theorem isTotallyAcyclic_of_injective (n : SimplexCategory)
    (O : Sheaf (topology C J) RingCat.{w}) (I : SheafOfModules.{w} O) [Injective I]
    [HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w})] :
    Sheaf.IsTotallyAcyclic
      ((stageRestrict C J AddCommGrpCat.{w} n).obj
        ((SheafOfModules.toSheaf O).obj I)) :=
  sorry

end CategoryTheory.SimplicialSites

namespace CategoryTheory.Grothendieck

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [IsFiberwiseSite F J]

/-- The restriction to any fiber of the underlying abelian sheaf of an injective module
over a ring sheaf on the total site of a fiberwise simplicial site is totally acyclic. -/
@[instance]
theorem isTotallyAcyclic_of_injective (n : SimplexCategory)
    (O : Sheaf (topology F J) RingCat.{w}) (I : SheafOfModules.{w} O) [Injective I]
    [HasSheafify ((J (op n)).toGrothendieck) AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w})] :
    Sheaf.IsTotallyAcyclic
      ((fiberRestrict F J AddCommGrpCat.{w} n).obj
        ((SheafOfModules.toSheaf O).obj I)) :=
  sorry

end CategoryTheory.Grothendieck
