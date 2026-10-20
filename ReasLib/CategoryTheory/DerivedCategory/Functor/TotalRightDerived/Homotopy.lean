/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Naturality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Induced.Cochain
public import ReasLib.CategoryTheory.Functor.Derived.Naturality.Right
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Total Right Derived Functors from the Homotopy Category

This file owns the construction-neutral unbounded total right derived functor, its homotopy- and
cochain-level units, and the corresponding universal-property statements.  It assumes only the
canonical `HasRightDerivedFunctor` instance and does not require K-injective resolutions.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe uA vA wA uB vB wB

namespace CategoryTheory.Functor.RightDerived.Homotopy

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]

/-- The total right derived functor of an additive functor, using its canonical functor from the
homotopy category to the target derived category. -/
@[stacks 05S9]
abbrev functor (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    DerivedCategory A ⥤ DerivedCategory B :=
  (Functor.Homotopy.toDerived F).totalRightDerived
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
    (HomotopyCategory.quasiIso A (up ℤ))

/-- The canonical unit from the homotopy-to-derived functor to its total right derived functor. -/
@[stacks 05S9]
noncomputable abbrev unit (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    Functor.Homotopy.toDerived F ⟶
      (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A) ⋙ functor F :=
  (Functor.Homotopy.toDerived F).totalRightDerivedUnit
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
    (HomotopyCategory.quasiIso A (up ℤ))

/-- The cochain-level unit comparing termwise application with the total right derived functor. -/
@[stacks 05S9]
noncomputable def cochainUnit (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    F.mapHomologicalComplex (up ℤ) ⋙
        (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B) ⟶
      (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A) ⋙ functor F :=
  (Functor.Homotopy.cochainIso F).inv ≫
    Functor.whiskerLeft (HomotopyCategory.quotient A (up ℤ)) (unit F) ≫
    (Functor.associator
      (HomotopyCategory.quotient A (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
      (functor F)).hom ≫
    (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso A) (functor F)).hom

/-- The homotopy-level unit exhibits `functor F` as a right derived functor. -/
@[stacks 05S9]
theorem isRightDerived (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    (functor F).IsRightDerivedFunctor (unit F)
      (HomotopyCategory.quasiIso A (up ℤ)) := sorry

/-- The cochain-level unit exhibits `functor F` as a right derived functor at quasi-isomorphisms. -/
@[stacks 05S9]
theorem cochainIsRightDerived (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    (functor F).IsRightDerivedFunctor (cochainUnit F)
      (HomologicalComplex.quasiIso A (up ℤ)) := sorry

/-- The natural transformation between total right-derived functors induced by a natural
transformation of additive functors. -/
@[stacks 05T2 "naturality of total right-derived functors"]
noncomputable def mapNatTrans {F G : A ⥤ B} [F.Additive] [G.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (τ : F ⟶ G) : functor F ⟶ functor G :=
  Functor.RightDerived.mapNatTrans
    (F := Functor.Homotopy.toDerived F)
    (G := Functor.Homotopy.toDerived G)
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
    (HomotopyCategory.quasiIso A (up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory B (up ℤ) ⥤ DerivedCategory B))

/-- The derived map is characterized by compatibility with the homotopy-level units. -/
@[stacks 05T2, reassoc (attr := simp)]
theorem mapNatTrans.fac {F G : A ⥤ B} [F.Additive] [G.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (τ : F ⟶ G) :
    unit F ≫ Functor.whiskerLeft
        (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
        (mapNatTrans τ) =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (up ℤ))
          (DerivedCategory.Qh : HomotopyCategory B (up ℤ) ⥤ DerivedCategory B) ≫
        unit G := sorry

/-- The derived map is also characterized on cochain complexes by compatibility with the
cochain-level units. -/
@[stacks 05T2, reassoc (attr := simp)]
theorem mapNatTrans.cochainFac {F G : A ⥤ B} [F.Additive] [G.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (τ : F ⟶ G) :
    cochainUnit F ≫ Functor.whiskerLeft
        (DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A)
        (mapNatTrans τ) =
      Functor.whiskerRight (NatTrans.mapHomologicalComplex τ (up ℤ))
          (DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B) ≫
        cochainUnit G := sorry

/-- Objectwise compatibility of the derived map with the cochain-level units. -/
@[stacks 05T2, reassoc (attr := simp)]
theorem mapNatTrans.cochainFac_app {F G : A ⥤ B} [F.Additive] [G.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (τ : F ⟶ G) (K : CochainComplex A ℤ) :
    (cochainUnit F).app K ≫
        (mapNatTrans τ).app
          ((DerivedCategory.Q : CochainComplex A ℤ ⥤ DerivedCategory A).obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (up ℤ)).app K) ≫
        (cochainUnit G).app K := sorry

/-- Deriving the identity natural transformation gives the identity transformation. -/
@[stacks 05T2, simp]
theorem mapNatTrans.id (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    mapNatTrans (𝟙 F) = 𝟙 (functor F) := sorry

/-- Derivation preserves composition of natural transformations. -/
@[stacks 05T2, simp]
theorem mapNatTrans.comp {F G H : A ⥤ B}
    [F.Additive] [G.Additive] [H.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (τ : F ⟶ G) (σ : G ⟶ H) :
    mapNatTrans (τ ≫ σ) = mapNatTrans τ ≫ mapNatTrans σ := sorry

/-- The isomorphism between total right-derived functors induced by a natural isomorphism of
additive functors. -/
@[stacks 05T2 "naturality of total right-derived functors"]
noncomputable def mapNatIso {F G : A ⥤ B} [F.Additive] [G.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (e : F ≅ G) : functor F ≅ functor G :=
  Functor.RightDerived.mapNatIso
    (F := Functor.Homotopy.toDerived F)
    (G := Functor.Homotopy.toDerived G)
    (DerivedCategory.Qh : HomotopyCategory A (up ℤ) ⥤ DerivedCategory A)
    (HomotopyCategory.quasiIso A (up ℤ))
    (Functor.isoWhiskerRight (NatIso.mapHomotopyCategory e (up ℤ))
      (DerivedCategory.Qh : HomotopyCategory B (up ℤ) ⥤ DerivedCategory B))

/-- The forward map of the derived isomorphism is the derived forward transformation. -/
@[stacks 05T2, simp]
theorem mapNatIso.hom {F G : A ⥤ B} [F.Additive] [G.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (e : F ≅ G) :
    (mapNatIso e).hom = mapNatTrans e.hom := sorry

/-- The inverse map of the derived isomorphism is the derived inverse transformation. -/
@[stacks 05T2, simp]
theorem mapNatIso.inv {F G : A ⥤ B} [F.Additive] [G.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (e : F ≅ G) :
    (mapNatIso e).inv = mapNatTrans e.inv := sorry

/-- Deriving the identity isomorphism gives the identity isomorphism. -/
@[stacks 05T2, simp]
theorem mapNatIso.refl (F : A ⥤ B) [F.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))] :
    mapNatIso (Iso.refl F) = Iso.refl (functor F) := sorry

/-- Derivation commutes with symmetry of natural isomorphisms. -/
@[stacks 05T2, simp]
theorem mapNatIso.symm {F G : A ⥤ B} [F.Additive] [G.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (e : F ≅ G) :
    mapNatIso e.symm = (mapNatIso e).symm := sorry

/-- Derivation preserves transitivity of natural isomorphisms. -/
@[stacks 05T2, simp]
theorem mapNatIso.trans {F G H : A ⥤ B}
    [F.Additive] [G.Additive] [H.Additive]
    [(Functor.Homotopy.toDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [(Functor.Homotopy.toDerived G).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    [(Functor.Homotopy.toDerived H).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (up ℤ))]
    (e : F ≅ G) (e' : G ≅ H) :
    mapNatIso (e ≪≫ e') = mapNatIso e ≪≫ mapNatIso e' := sorry


-- The isomorphism laws in `mapNatIso` are Prop-valued fields; its forward and inverse maps are
-- the explicit canonical transformations supplied by total right-derived naturality.

end CategoryTheory.Functor.RightDerived.Homotopy
