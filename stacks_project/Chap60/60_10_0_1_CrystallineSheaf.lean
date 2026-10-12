/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap60.«60_8_1_1»
public import stacks_project.Chap60.«60_9_1_1_Site»

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline

universe u v

noncomputable section

/-- Inverse image of a Type-valued Zariski sheaf along the underlying continuous map of a
thickening morphism. -/
def crystallineInverseImage (C : Type v) [Category C]
    (thickening : C ⥤ Scheme.{u}) {A B : C} (f : A ⟶ B) :
    TopCat.Sheaf (Type u) (thickening.obj B).toTopCat ⥤
      TopCat.Sheaf (Type u) (thickening.obj A).toTopCat :=
  TopCat.Sheaf.pullback (Type u) (thickening.map f).base

/- A crystalline sheaf is a compatible family of sheaves on the schemes supplied by a
   thickening functor. -/
/-- A compatible family of sheaves on the schemes supplied by a thickening functor. -/
structure CrystallineSheaf (C : Type v) [Category C]
    (thickening : C ⥤ Scheme.{u}) where
  /-- The sheaf assigned to each object of the crystalline category. -/
  obj : ∀ A : C, TopCat.Sheaf (Type u) (thickening.obj A).toTopCat
  /-- The comparison map from the pullback along a crystalline morphism. -/
  comparison : ∀ {A B : C} (f : A ⟶ B),
    (crystallineInverseImage C thickening f).obj (obj B) ⟶ obj A

/-- Construct a crystalline sheaf from its objectwise sheaves and comparison family. -/
def CrystallineSheaf.of {C : Type v} [Category C]
    (thickening : C ⥤ Scheme.{u})
    (obj : ∀ A : C, TopCat.Sheaf (Type u) (thickening.obj A).toTopCat)
    (comparison : ∀ {A B : C} (f : A ⟶ B),
      (crystallineInverseImage C thickening f).obj (obj B) ⟶ obj A) :
    CrystallineSheaf C thickening :=
  { obj, comparison }

/-- Comparison maps along open immersions are isomorphisms. -/
theorem CrystallineSheaf.isIso_of_isOpenImmersion {C : Type v} [Category C]
    {thickening : C ⥤ Scheme.{u}} (F : CrystallineSheaf C thickening)
    {A B : C} (f : A ⟶ B) [IsOpenImmersion (thickening.map f)] :
    IsIso (F.comparison f) :=
  sorry

namespace AlgebraicGeometry.Scheme.Crystalline

/-- The functor sending a relative crystalline object to its thickening scheme. -/
def thickeningFunctor
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :
    RelativeCRIS S I γ h_compatible X x₀ ⥤ Scheme.{u} where
  obj := fun A ↦ A.1.thickening
  map := fun f ↦ f.thickening
  map_id := sorry
  map_comp := sorry

/-- The functor sending a small crystalline object to its thickening scheme. -/
def smallThickeningFunctor
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :
    smallCrystallineSite S I γ h_compatible X x₀ ⥤ Scheme.{u} where
  obj := fun A ↦ A.obj.1.thickening
  map := fun f ↦ f.hom.thickening
  map_id := sorry
  map_comp := sorry

end AlgebraicGeometry.Scheme.Crystalline

namespace CrystallineSheaf

/-- The compatible-family owner for the big crystalline category. -/
abbrev Big
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :=
  CrystallineSheaf (RelativeCRIS S I γ h_compatible X x₀)
    (AlgebraicGeometry.Scheme.Crystalline.thickeningFunctor S I γ h_compatible X x₀)

/-- The compatible-family owner for the small crystalline category. -/
abbrev Small
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme) :=
  CrystallineSheaf (smallCrystallineSite S I γ h_compatible X x₀)
    (AlgebraicGeometry.Scheme.Crystalline.smallThickeningFunctor S I γ h_compatible X x₀)

end CrystallineSheaf
