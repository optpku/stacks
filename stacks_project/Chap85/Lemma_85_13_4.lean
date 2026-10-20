/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.CategoryTheory.Sites.Simplicial.IntegerPostnikov
public import ReasLib.CategoryTheory.Sites.Grothendieck.IntegerPostnikov

/-!
# Lemma 85.13.4

Integer-resolution tensor Postnikov towers and their homotopy colimits in both
presentations of a simplicial site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.DerivedCategory
open HomologicalComplex
open scoped CategoryTheory.DerivedCategory.DerivedTensor

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
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget AddCommGrpCat.{w})]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [HasDerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})]
variable [∀ (K L : CochainComplex (Sheaf (topology C J) AddCommGrpCat.{w}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf (topology C J) AddCommGrpCat.{w})) (ComplexShape.up ℤ)]
variable [DerivedTensor.Right.Has (C := (Sheaf (topology C J) AddCommGrpCat.{w}))]
variable (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))

/- Lemma 85.13.4 (Postnikov system): the integer-resolution tensor stages and
canonical maps form a Postnikov tower. -/
@[stacks 0D9I] #check (CategoryTheory.SimplicialSites.IntegerPostnikov.tower C J K :
  PostnikovSystem.Tower (DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w})))

#check (CategoryTheory.SimplicialSites.IntegerPostnikov.tower_X C J K :
  ∀ n : ℕ, (CategoryTheory.SimplicialSites.IntegerPostnikov.tower C J K).X n =
    CategoryTheory.SimplicialSites.IntegerPostnikov.X C J K n)

/- Lemma 85.13.4 (homotopy colimit): the canonical sequence of shifted stages
has homotopy colimit K. -/
@[stacks 0D9I] #check (CategoryTheory.SimplicialSites.abelianPostnikov_isHocolim C J K :
  HomotopyColimit.IsOf (CategoryTheory.SimplicialSites.IntegerPostnikov.shiftedAux C J K) K)

end CategoryTheory.SimplicialSites

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
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w},
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [HasSheafify (topology F J) AddCommGrpCat.{w}]
variable [HasDerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})]
variable [∀ (K L : CochainComplex (Sheaf (topology F J) AddCommGrpCat.{w}) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (curriedTensor (Sheaf (topology F J) AddCommGrpCat.{w})) (ComplexShape.up ℤ)]
variable [DerivedTensor.Right.Has (C := (Sheaf (topology F J) AddCommGrpCat.{w}))]
variable (K : DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w}))

/- Lemma 85.13.4 (Postnikov system): the integer-resolution tensor stages and
canonical maps form a Postnikov tower. -/
@[stacks 0D9I] #check (CategoryTheory.Grothendieck.IntegerPostnikov.tower F J K :
  PostnikovSystem.Tower (DerivedCategory (Sheaf (topology F J) AddCommGrpCat.{w})))

#check (CategoryTheory.Grothendieck.IntegerPostnikov.tower_X F J K :
  ∀ n : ℕ, (CategoryTheory.Grothendieck.IntegerPostnikov.tower F J K).X n =
    CategoryTheory.Grothendieck.IntegerPostnikov.X F J K n)

/- Lemma 85.13.4 (homotopy colimit): the canonical sequence of shifted stages
has homotopy colimit K. -/
@[stacks 0D9I] #check (CategoryTheory.Grothendieck.fiberAbelianPostnikov_isHocolim F J K :
  HomotopyColimit.IsOf (CategoryTheory.Grothendieck.IntegerPostnikov.shiftedAux F J K) K)

end CategoryTheory.Grothendieck
