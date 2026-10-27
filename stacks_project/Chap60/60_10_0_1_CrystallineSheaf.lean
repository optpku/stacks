/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Sheaf

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline

universe u v

section Families

variable (C : Type v) [Category C] (thickening : C ⥤ Scheme.{u})

/- Inverse image along a morphism between thickening schemes. -/
#check (crystallineInverseImage C thickening : ∀ {A B : C},
  (A ⟶ B) → TopCat.Sheaf (Type u) (thickening.obj B).toTopCat ⥤
    TopCat.Sheaf (Type u) (thickening.obj A).toTopCat)

/- A family supplies a sheaf on each thickening. -/
#check (CrystallineSheaf.obj : CrystallineSheaf C thickening → ∀ (A : C),
  TopCat.Sheaf (Type u) (thickening.obj A).toTopCat)

/- A family supplies a chosen comparison map for each morphism. -/
#check (CrystallineSheaf.comparison : ∀ (F : CrystallineSheaf C thickening)
    {A B : C} (f : A ⟶ B),
  (crystallineInverseImage C thickening f).obj (F.obj B) ⟶ F.obj A)

/- Families are constructed from their sheaves and comparison maps. -/
#check (CrystallineSheaf.of thickening :
  ∀ (obj : ∀ A : C, TopCat.Sheaf (Type u) (thickening.obj A).toTopCat),
    (∀ {A B : C} (f : A ⟶ B),
      (crystallineInverseImage C thickening f).obj (obj B) ⟶ obj A) →
    CrystallineSheaf C thickening)

end Families

variable (S : Scheme.{u}) (I : S.IdealSheafData)
  (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
  (h_compatible : ∀ (V : S.affineOpens) (g : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen g))
      (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom)
  (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)

/- The big crystalline category has its canonical projection to thickening schemes. -/
#check (AlgebraicGeometry.Scheme.Crystalline.thickeningFunctor S I γ h_compatible X x₀ :
  RelativeCRIS S I γ h_compatible X x₀ ⥤ Scheme.{u})

/- The small crystalline category has its canonical projection to thickening schemes. -/
#check (AlgebraicGeometry.Scheme.Crystalline.smallThickeningFunctor S I γ h_compatible X x₀ :
  smallCrystallineSite S I γ h_compatible X x₀ ⥤ Scheme.{u})

/- Big crystalline families use the canonical thickening functor. -/
#check (CrystallineSheaf.Big S I γ h_compatible X x₀ : Type (u + 1))

/- Small crystalline families use the canonical thickening functor. -/
#check (CrystallineSheaf.Small S I γ h_compatible X x₀ : Type (u + 1))
