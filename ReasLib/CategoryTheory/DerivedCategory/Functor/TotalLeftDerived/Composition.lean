module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalLeftDerived

@[expose] public section

/-!
# Composition of total left derived functors

@stack 05T2
@stack 0FTH

For composable additive functors between abelian categories, this module constructs the canonical
comparison from the composite of their total left derived functors to the total left derived
functor of their composite.  The comparison becomes an isomorphism precisely when the iterated
model satisfies the corresponding derived-functor compatibility condition.

This distinction is essential: composition of left derived functors is not unconditionally a left
derived functor of the composite.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe uA vA wA uB vB wB uC vC wC

namespace CategoryTheory.Functor.LeftDerived.Homotopy.Composition

section

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wB} B]
variable [HasDerivedCategory.{wC} C]

/-- The homotopy-to-derived functor of an underived composite is canonically identified with the
composite obtained by first mapping to the homotopy category and then applying the second
functor's homotopy-to-derived functor. -/
noncomputable abbrev toDerivedIso
    (F : B ⥤ A)
    (G : C ⥤ B)
    (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H ≅ G ⋙ F) :
    Functor.Homotopy.toDerived H ≅
      G.mapHomotopyCategory (up ℤ) ⋙ Functor.Homotopy.toDerived F :=
  Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso hcomp.symm (up ℤ)).symm
      (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ≪≫
    Functor.associator
      (G.mapHomotopyCategory (up ℤ))
      (F.mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)

/-- The iterated counit from the composite of total left derived functors to the corresponding
composite homotopy-category functor.  It is candidate derived-functor data; universality is an
additional compatibility condition. -/
noncomputable abbrev counit
    (F : B ⥤ A)
    (G : C ⥤ B)
    [F.Additive] [G.Additive]
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))] :
    (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C) ⋙
      (LeftDerived.Homotopy.functor G ⋙ LeftDerived.Homotopy.functor F) ⟶
      G.mapHomotopyCategory (up ℤ) ⋙ Functor.Homotopy.toDerived F :=
  (Functor.associator
      (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)
      (LeftDerived.Homotopy.functor G)
      (LeftDerived.Homotopy.functor F)).inv ≫
    Functor.whiskerRight
      (LeftDerived.Homotopy.counit G)
      (LeftDerived.Homotopy.functor F) ≫
    (Functor.associator
      (G.mapHomotopyCategory (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory B (up ℤ) ⥤ DerivedCategory B)
      (LeftDerived.Homotopy.functor F)).hom ≫
    Functor.whiskerLeft
      (G.mapHomotopyCategory (up ℤ))
      (LeftDerived.Homotopy.counit F)

/-- The canonical comparison from the iterated total left derived functor to the total left
derived functor of the composite.  It exists without any composition-compatibility hypothesis. -/
@[stacks 05T2]
noncomputable def comparison
    (F : B ⥤ A)
    (G : C ⥤ B)
    (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H ≅ G ⋙ F)
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))] :
    LeftDerived.Homotopy.functor G ⋙ LeftDerived.Homotopy.functor F ⟶
      LeftDerived.Homotopy.functor H :=
  (LeftDerived.Homotopy.functor H).leftDerivedLift
    (LeftDerived.Homotopy.counit H)
    (HomotopyCategory.quasiIso C (up ℤ))
    (LeftDerived.Homotopy.functor G ⋙ LeftDerived.Homotopy.functor F)
    (counit F G ≫ (toDerivedIso F G H hcomp).inv)

/-- The composition comparison is characterized by its equation with the canonical derived
counits. -/
@[reassoc (attr := simp)]
theorem comparison_fac
    (F : B ⥤ A)
    (G : C ⥤ B)
    (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H ≅ G ⋙ F)
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))] :
    Functor.whiskerLeft
        (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)
        (comparison F G H hcomp) ≫
      LeftDerived.Homotopy.counit H =
        counit F G ≫ (toDerivedIso F G H hcomp).inv := by
  exact (LeftDerived.Homotopy.functor H).leftDerived_fac
    (LeftDerived.Homotopy.counit H)
    (HomotopyCategory.quasiIso C (up ℤ))
    (LeftDerived.Homotopy.functor G ⋙ LeftDerived.Homotopy.functor F)
    (counit F G ≫ (toDerivedIso F G H hcomp).inv)

/-- The componentwise equation characterizing the total-left-derived composition comparison. -/
theorem comparison_fac_app
    (F : B ⥤ A)
    (G : C ⥤ B)
    (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H ≅ G ⋙ F)
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    (K : HomotopyCategory C (up ℤ)) :
    (comparison F G H hcomp).app
        ((DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).obj K) ≫
      (LeftDerived.Homotopy.counit H).app K =
        (counit F G).app K ≫ (toDerivedIso F G H hcomp).inv.app K := by
  exact (LeftDerived.Homotopy.functor H).leftDerived_fac_app
    (LeftDerived.Homotopy.counit H)
    (HomotopyCategory.quasiIso C (up ℤ))
    (LeftDerived.Homotopy.functor G ⋙ LeftDerived.Homotopy.functor F)
    (counit F G ≫ (toDerivedIso F G H hcomp).inv) K

/-- The iterated model is a left derived functor exactly when the canonical composition
comparison is invertible. -/
theorem isLeftDerivedFunctor_iff_isIso_comparison
    (F : B ⥤ A)
    (G : C ⥤ B)
    (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H ≅ G ⋙ F)
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))] :
    (LeftDerived.Homotopy.functor G ⋙ LeftDerived.Homotopy.functor F).IsLeftDerivedFunctor
        (counit F G) (HomotopyCategory.quasiIso C (up ℤ)) ↔
      IsIso (comparison F G H hcomp) := by
  rw [isLeftDerivedFunctor_iff_isRightKanExtension]
  rw [isRightKanExtension_iff_of_iso₂
    (counit F G)
    (counit F G ≫ (toDerivedIso F G H hcomp).inv)
    (toDerivedIso F G H hcomp).symm (Iso.refl _) (by simp)]
  rw [← isLeftDerivedFunctor_iff_isRightKanExtension
    (LeftDerived.Homotopy.functor G ⋙ LeftDerived.Homotopy.functor F)
    (counit F G ≫ (toDerivedIso F G H hcomp).inv)
    (HomotopyCategory.quasiIso C (up ℤ))]
  exact (LeftDerived.Homotopy.functor H).isLeftDerivedFunctor_iff_isIso_leftDerivedLift
    (LeftDerived.Homotopy.counit H)
    (HomotopyCategory.quasiIso C (up ℤ))
    (LeftDerived.Homotopy.functor G ⋙ LeftDerived.Homotopy.functor F)
    (counit F G ≫ (toDerivedIso F G H hcomp).inv)

/-- A derived-functor compatibility witness makes the canonical composition comparison
invertible. -/
instance comparison_isIso
    (F : B ⥤ A)
    (G : C ⥤ B)
    (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H ≅ G ⋙ F)
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [(LeftDerived.Homotopy.functor G ⋙ LeftDerived.Homotopy.functor F).IsLeftDerivedFunctor
      (counit F G) (HomotopyCategory.quasiIso C (up ℤ))] :
    IsIso (comparison F G H hcomp) :=
  (isLeftDerivedFunctor_iff_isIso_comparison F G H hcomp).1 inferInstance

/-- The composition comparison as an isomorphism, under the explicit hypothesis that it is
invertible. -/
@[stacks 0FTH "derived pullback-tensor composition",
  stacks 0FTI "composition of derived pullbacks"]
noncomputable def iso
    (F : B ⥤ A)
    (G : C ⥤ B)
    (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H ≅ G ⋙ F)
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [IsIso (comparison F G H hcomp)] :
    LeftDerived.Homotopy.functor G ⋙ LeftDerived.Homotopy.functor F ≅
      LeftDerived.Homotopy.functor H :=
  asIso (comparison F G H hcomp)

/-- The forward morphism of the composition isomorphism is the canonical comparison. -/
@[simp]
theorem iso_hom
    (F : B ⥤ A)
    (G : C ⥤ B)
    (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H ≅ G ⋙ F)
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [IsIso (comparison F G H hcomp)] :
    (iso F G H hcomp).hom = comparison F G H hcomp := rfl

/-- The total-left-derived composition isomorphism is characterized by its equation with the
canonical derived counits. -/
theorem iso_hom_counit
    (F : B ⥤ A)
    (G : C ⥤ B)
    (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H ≅ G ⋙ F)
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [IsIso (comparison F G H hcomp)] :
    Functor.whiskerLeft
        (DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C)
        (iso F G H hcomp).hom ≫
      LeftDerived.Homotopy.counit H =
        counit F G ≫
          (toDerivedIso F G H hcomp).inv := by
  simpa only [iso_hom] using comparison_fac F G H hcomp

/-- The componentwise counit equation characterizing the total-left-derived composition
isomorphism. -/
theorem iso_hom_counit_app
    (F : B ⥤ A)
    (G : C ⥤ B)
    (H : C ⥤ A)
    [F.Additive] [G.Additive] [H.Additive]
    (hcomp : H ≅ G ⋙ F)
    [(Functor.Homotopy.toDerived F).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso B (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso C (up ℤ))]
    [IsIso (comparison F G H hcomp)]
    (K : HomotopyCategory C (up ℤ)) :
    (iso F G H hcomp).hom.app
        ((DerivedCategory.Qh : HomotopyCategory C (up ℤ) ⥤ DerivedCategory C).obj K) ≫
      (LeftDerived.Homotopy.counit H).app K =
        (counit F G).app K ≫
          (toDerivedIso F G H hcomp).inv.app K := by
  exact NatTrans.congr_app (iso_hom_counit F G H hcomp) K

end

end CategoryTheory.Functor.LeftDerived.Homotopy.Composition
