/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.Acyclic

/-!
# Lemma 85.6.2

In Situation 85.3.3, if `O` is a sheaf of rings on `C_total` and `I` is injective
in `Mod(O)`, then the degree-`n` restriction `I_n` is a totally acyclic sheaf on
`C_n`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

universe u v w

/- Lemma 85.6.2 (1): in Situation 85.3.3 case A, if `O` is a sheaf of rings on
`C_total` and `I` is injective in `Mod(O)`, then the restriction `I_n` is a
totally acyclic sheaf on `C_n`. -/
@[stacks 0D73] #check (CategoryTheory.SimplicialSites.isTotallyAcyclic_of_injective :
  ∀ (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
    [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
    [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
      ((C.map φ).toFunctor).op.HasLeftKanExtension P]
    [CategoryTheory.SimplicialSites.IsMorphismDiagram C J]
    (n : SimplexCategory)
    (O : Sheaf (CategoryTheory.SimplicialSites.topology C J) RingCat.{w})
    (I : SheafOfModules.{w} O) [Injective I]
    [HasSheafify ((J n).toGrothendieck) AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf ((J n).toGrothendieck) AddCommGrpCat.{w})],
    Sheaf.IsTotallyAcyclic
      ((CategoryTheory.SimplicialSites.stageRestrict C J AddCommGrpCat.{w} n).obj
        ((SheafOfModules.toSheaf O).obj I)))

/- Lemma 85.6.2 (2): in Situation 85.3.3 case B, if `O` is a sheaf of rings on
`C_total` and `I` is injective in `Mod(O)`, then the restriction `I_n` is a
totally acyclic sheaf on `C_n`. -/
@[stacks 0D73] #check (CategoryTheory.Grothendieck.isTotallyAcyclic_of_injective :
  ∀ (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
    [CategoryTheory.Grothendieck.IsFiberwiseSite F J]
    (n : SimplexCategory)
    (O : Sheaf (CategoryTheory.Grothendieck.topology F J) RingCat.{w})
    (I : SheafOfModules.{w} O) [Injective I]
    [HasSheafify ((J (op n)).toGrothendieck) AddCommGrpCat.{w}]
    [HasExt.{w} (Sheaf ((J (op n)).toGrothendieck) AddCommGrpCat.{w})],
    Sheaf.IsTotallyAcyclic
      ((CategoryTheory.Grothendieck.fiberRestrict F J AddCommGrpCat.{w} n).obj
        ((SheafOfModules.toSheaf O).obj I)))
