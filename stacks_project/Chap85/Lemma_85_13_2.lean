/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedSystem.Gluing
public import ReasLib.CategoryTheory.Sites.Grothendieck.DerivedSystem
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Functor

universe u v w

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [SimplicialSites.IsMorphismDiagram.{u, v, w} C J]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (SimplicialSites.topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

variable (F : SimplicialObject Cat.{v, u}) (JF : ∀ n, Precoverage (F.obj n))
variable [Grothendieck.IsFiberwiseSite F JF]
variable [∀ n, HasWeakSheafify (JF n).toGrothendieck (Type w)]
variable [HasWeakSheafify (Grothendieck.topology F JF) (Type w)]
variable [HasSheafify (Grothendieck.topology F JF) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (JF n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/- Lemma 85.13.2 (1): in the covariant presentation, canonical derived restrictions
and transitions form a simplicial derived system. -/
@[stacks 0D9H] #check
  (CategoryTheory.SimplicialSites.toDerivedSystem C J :
    DerivedCategory (Sheaf (SimplicialSites.topology C J) AddCommGrpCat.{w}) →
      SimplicialSites.DerivedSystem (fun n ↦ (J n).toGrothendieck)
        (fun φ ↦ (SimplicialSites.abelianInverseImageExact C J φ).obj)
        (SimplicialSites.AbelianDerived.inverseImageCompIso C J))

/- Lemma 85.13.2 (2): in the covariant presentation, the restriction system of a
cartesian total derived object is cartesian. -/
@[stacks 0D9H] #check
  (CategoryTheory.SimplicialSites.toDerivedSystem_isCartesian C J :
    ∀ (K : DerivedCategory (Sheaf (SimplicialSites.topology C J) AddCommGrpCat.{w}))
      [SimplicialSites.AbelianDerived.IsCartesian C J K],
      SimplicialSites.DerivedSystem.IsCartesian (SimplicialSites.toDerivedSystem C J K))

/- Lemma 85.13.2 (3): in the fiberwise presentation, canonical derived restrictions
and transitions form a simplicial derived system. -/
@[stacks 0D9H] #check
  (CategoryTheory.Grothendieck.toDerivedSystem F JF :
    DerivedCategory (Sheaf (Grothendieck.topology F JF) AddCommGrpCat.{w}) →
      SimplicialSites.DerivedSystem (fun n ↦ (JF (op n)).toGrothendieck)
        (fun φ ↦ (Grothendieck.abelianInverseImageExact F JF φ).obj)
        (Grothendieck.AbelianDerived.inverseImageCompIso F JF))

/- Lemma 85.13.2 (4): in the fiberwise presentation, the restriction system of a
cartesian total derived object is cartesian. -/
@[stacks 0D9H] #check
  (CategoryTheory.Grothendieck.toDerivedSystem_isCartesian F JF :
    ∀ (K : DerivedCategory (Sheaf (Grothendieck.topology F JF) AddCommGrpCat.{w}))
      [Grothendieck.AbelianDerived.IsCartesian F JF K],
      SimplicialSites.DerivedSystem.IsCartesian (Grothendieck.toDerivedSystem F JF K))
