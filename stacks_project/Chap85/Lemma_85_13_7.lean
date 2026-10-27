/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Simplicial.DerivedSystem.Gluing
public import ReasLib.CategoryTheory.Sites.Grothendieck.DerivedSystem.Gluing
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialSites CategoryTheory.Limits Opposite Functor

universe u v w

section CaseA

variable (C : SimplexCategory ⥤ Cat.{v, u}) (J : ∀ n, Precoverage (C.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram.{u, v, w} C J]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (topology C J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]

/- Lemma 85.13.7 (1): in case A, the covariant presentation by morphisms of sites,
a cartesian derived system with positive shifted self-Hom vanishing has a cartesian
realization. -/
@[stacks 0D9L] #check
  (CategoryTheory.SimplicialSites.exists_isCartesian_of_derivedSystem C J :
    ∀ (Ksys : DerivedSystem (fun n ↦ (J n).toGrothendieck)
      (fun φ ↦ (abelianInverseImageExact C J φ).obj)
      (AbelianDerived.inverseImageCompIso C J)),
    DerivedSystem.IsCartesian Ksys →
    (∀ (n : SimplexCategory) (t : ℤ), 0 < t →
      Subsingleton ((Ksys.obj n)⟦t⟧ ⟶ Ksys.obj n)) →
      ∃ (K : DerivedCategory (Sheaf (topology C J) AddCommGrpCat.{w}))
      (α : DerivedSystem.Hom (toDerivedSystem C J K) Ksys),
      AbelianDerived.IsCartesian C J K ∧ ∀ n, IsIso (α.app n))

end CaseA

section CaseB

variable (F : SimplicialObject Cat.{v, u}) (J : ∀ n, Precoverage (F.obj n))
variable [Grothendieck.IsFiberwiseSite F J]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [HasWeakSheafify (Grothendieck.topology F J) (Type w)]
variable [UnivLE.{max u v, w}]
variable [HasSheafify (Grothendieck.topology F J) AddCommGrpCat.{w}]
variable [∀ n, HasSheafify (J n).toGrothendieck AddCommGrpCat.{w}]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ AddCommGrpCat.{w}),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

/- Lemma 85.13.7 (2): in case B, the fiberwise presentation by cocontinuous functors
with property P, a cartesian derived system with positive shifted self-Hom vanishing
has a cartesian realization. -/
@[stacks 0D9L] #check
  (CategoryTheory.Grothendieck.exists_isCartesian_of_derivedSystem F J :
    ∀ (Ksys : SimplicialSites.DerivedSystem (fun n ↦ (J (op n)).toGrothendieck)
      (fun φ ↦ (Grothendieck.abelianInverseImageExact F J φ).obj)
      (Grothendieck.AbelianDerived.inverseImageCompIso F J)),
    SimplicialSites.DerivedSystem.IsCartesian Ksys →
    (∀ (n : SimplexCategory) (t : ℤ), 0 < t →
      Subsingleton ((Ksys.obj n)⟦t⟧ ⟶ Ksys.obj n)) →
      ∃ (K : DerivedCategory (Sheaf (Grothendieck.topology F J) AddCommGrpCat.{w}))
      (α : SimplicialSites.DerivedSystem.Hom (Grothendieck.toDerivedSystem F J K) Ksys),
      Grothendieck.AbelianDerived.IsCartesian F J K ∧ ∀ n, IsIso (α.app n))

end CaseB
