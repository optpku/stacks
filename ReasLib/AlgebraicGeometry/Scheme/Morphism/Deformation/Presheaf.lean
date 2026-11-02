/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

variable {S X X' Y Y' : Scheme.{u}}

/-- Restriction of a compatible local deformation along an inclusion of opens. -/
def restrictSection (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    {U' V' : X'.Opens} (h : V' ≤ U') :
    sections S i j a A U' → sections S i j a A V' :=
  fun s ↦ ⟨restrictHom h s.1, mem_sections_restrictHom S i j a A h s.1 s.2⟩

/-- The underlying scheme morphism of a restricted compatible deformation is `restrictHom`. -/
theorem restrictSection_val (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    {U' V' : X'.Opens} (h : V' ≤ U') (s : sections S i j a A U') :
    (restrictSection S i j a A h s).1 = restrictHom h s.1 := by
  rfl

/-- Restriction of compatible local deformations along the identity inclusion is the identity. -/
theorem restrictSection_id (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    (U' : X'.Opens) :
    TypeCat.ofHom (restrictSection S i j a A (le_refl U')) = 𝟙 _ := by
  apply TypeCat.homEquiv.injective
  funext s
  apply Subtype.ext
  change X'.homOfLE (le_refl U') ≫ s.1 = s.1
  rw [Scheme.homOfLE_rfl, Category.id_comp]

/-- Successive restrictions of compatible local deformations equal restriction along the
composite inclusion. -/
theorem restrictSection_comp (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    {U' V' W' : X'.Opens} (hVU : V' ≤ U') (hWV : W' ≤ V') :
    TypeCat.ofHom (restrictSection S i j a A (hWV.trans hVU)) =
      TypeCat.ofHom (restrictSection S i j a A hVU) ≫
        TypeCat.ofHom (restrictSection S i j a A hWV) := by
  apply TypeCat.homEquiv.injective
  funext s
  apply Subtype.ext
  change X'.homOfLE (hWV.trans hVU) ≫ s.1 =
    X'.homOfLE hWV ≫ X'.homOfLE hVU ≫ s.1
  rw [← Category.assoc, Scheme.homOfLE_homOfLE]

/-- The presheaf of compatible local deformations with prescribed conormal map. -/
def presheaf (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) : TopCat.Presheaf (Type u) X' where
  obj U' := sections S i j a A U'.unop
  map h := TypeCat.ofHom (restrictSection S i j a A h.unop.le)
  map_id U' := restrictSection_id S i j a A U'.unop
  map_comp f g := restrictSection_comp S i j a A f.unop.le g.unop.le

/-- The value of the deformation presheaf on an open is the type of compatible local
deformations on that open. -/
theorem presheaf_obj (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    (U' : X'.Opens) :
    (presheaf S i j a A).obj (op U') = sections S i j a A U' := by
  rfl

/-- The deformation presheaf restricts sections using `restrictHom`. -/
theorem presheaf_map_apply (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i)
    {U' V' : (X'.Opens)ᵒᵖ} (h : U' ⟶ V') (s : (presheaf S i j a A).obj U') :
    ((presheaf S i j a A).map h s).1 = restrictHom h.unop.le s.1 := by
  rfl

/-- Compatible local deformations with a prescribed conormal map form a sheaf of sets. -/
theorem presheaf_isSheaf (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) :
    TopCat.Presheaf.IsSheaf (presheaf S i j a A) := sorry

/-- The type-valued sheaf of compatible local deformations with prescribed conormal map. -/
noncomputable def sheaf (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) : TopCat.Sheaf (Type u) X'.toTopCat :=
  ⟨presheaf S i j a A, presheaf_isSheaf i j a A⟩

/-- The value of the deformation sheaf on `U'` is the type of compatible local deformations
on `U'`. -/
theorem sheaf_obj (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y') (a : X ⟶ Y)
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (A : (Scheme.Modules.pullback a).obj (Scheme.Hom.conormalSheaf j) ⟶
      Scheme.Hom.conormalSheaf i) (U' : X'.Opens) :
    (sheaf S i j a A).1.obj (op U') = sections S i j a A U' := by
  rfl

end AlgebraicGeometry.Scheme.Hom.Deformation
