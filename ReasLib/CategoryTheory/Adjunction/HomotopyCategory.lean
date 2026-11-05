/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Adjunction.Basic
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Map
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction.Adjunction

@[expose] public section

/-!
# Adjunctions on homotopy categories

This module transports an adjunction of additive functors degreewise to complexes and then
to cochain homotopy categories using explicit units and counits. Component formulas and the
induced Hom-set equivalence on quotient representatives are available for derived constructions.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Adjunction

/-- The chain-complex adjunction induced by an adjunction of additive functors. -/
@[stacks 0DVC "adjunction on cochain complexes"]
noncomputable def mapHomologicalComplexAdjunction
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F) (c : ComplexShape ℤ) :
    G.mapHomologicalComplex c ⊣ F.mapHomologicalComplex c :=
  let unit : 𝟭 (HomologicalComplex D c) ⟶
      G.mapHomologicalComplex c ⋙ F.mapHomologicalComplex c :=
    { app := fun K =>
        { f := fun i => adj.unit.app (K.X i)
          comm' := by
            intro i j hij
            change adj.unit.app (K.X i) ≫ F.map (G.map (K.d i j)) =
              K.d i j ≫ adj.unit.app (K.X j)
            exact (adj.unit.naturality (K.d i j)).symm }
      naturality := by
        intro K L g
        apply HomologicalComplex.hom_ext
        intro i
        exact adj.unit.naturality (g.f i) }
  let counit : F.mapHomologicalComplex c ⋙ G.mapHomologicalComplex c ⟶
      𝟭 (HomologicalComplex C c) :=
    { app := fun K =>
        { f := fun i => adj.counit.app (K.X i)
          comm' := by
            intro i j hij
            change adj.counit.app (K.X i) ≫ K.d i j =
              G.map (F.map (K.d i j)) ≫ adj.counit.app (K.X j)
            exact (adj.counit.naturality (K.d i j)).symm }
      naturality := by
        intro K L g
        apply HomologicalComplex.hom_ext
        intro i
        exact adj.counit.naturality (g.f i) }
  {
    unit := unit
    counit := counit
    left_triangle_components := by
      intro K
      apply HomologicalComplex.hom_ext
      intro i
      change G.map (adj.unit.app (K.X i)) ≫
        adj.counit.app (G.obj (K.X i)) = 𝟙 _
      exact adj.left_triangle_components (K.X i)
    right_triangle_components := by
      intro K
      apply HomologicalComplex.hom_ext
      intro i
      change adj.unit.app (F.obj (K.X i)) ≫
        F.map (adj.counit.app (K.X i)) = 𝟙 _
      exact adj.right_triangle_components (K.X i) }

/-- An adjunction of additive functors induces an adjunction on homotopy categories of cochain
complexes. -/
noncomputable def mapHomotopyCategoryAdjunction
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F) :
    G.mapHomotopyCategory (up ℤ) ⊣ F.mapHomotopyCategory (up ℤ) :=
  let adj := mapHomologicalComplexAdjunction adj (up ℤ)
  let unit : 𝟭 (HomotopyCategory D (up ℤ)) ⟶
      G.mapHomotopyCategory (up ℤ) ⋙ F.mapHomotopyCategory (up ℤ) :=
    { app := fun K =>
        (HomotopyCategory.quotient D (up ℤ)).map (adj.unit.app K.as)
      naturality := by
        rintro ⟨K⟩ ⟨L⟩ ⟨g⟩
        change
          (HomotopyCategory.quotient D (up ℤ)).map
              (g ≫ adj.unit.app L) =
            (HomotopyCategory.quotient D (up ℤ)).map
              (adj.unit.app K ≫
                (G.mapHomologicalComplex (up ℤ) ⋙
                  F.mapHomologicalComplex (up ℤ)).map g)
        exact congrArg
          (fun k => (HomotopyCategory.quotient D (up ℤ)).map k)
          (adj.unit.naturality g) }
  let counit : F.mapHomotopyCategory (up ℤ) ⋙ G.mapHomotopyCategory (up ℤ) ⟶
      𝟭 (HomotopyCategory C (up ℤ)) :=
    { app := fun K =>
        (HomotopyCategory.quotient C (up ℤ)).map (adj.counit.app K.as)
      naturality := by
        rintro ⟨K⟩ ⟨L⟩ ⟨g⟩
        change
          (HomotopyCategory.quotient C (up ℤ)).map
              ((F.mapHomologicalComplex (up ℤ) ⋙
                G.mapHomologicalComplex (up ℤ)).map g ≫ adj.counit.app L) =
            (HomotopyCategory.quotient C (up ℤ)).map
              (adj.counit.app K ≫ g)
        exact congrArg
          (fun k => (HomotopyCategory.quotient C (up ℤ)).map k)
          (adj.counit.naturality g) }
  {
    unit := unit
    counit := counit
    left_triangle_components := by
      intro K
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      dsimp [unit, counit]
      change
        (HomotopyCategory.quotient C (up ℤ)).map
              ((G.mapHomologicalComplex (up ℤ)).map
                (adj.unit.app K)) ≫
            (HomotopyCategory.quotient C (up ℤ)).map
              (adj.counit.app
                ((G.mapHomologicalComplex (up ℤ)).obj K)) =
          𝟙 ((HomotopyCategory.quotient C (up ℤ)).obj
            ((G.mapHomologicalComplex (up ℤ)).obj K))
      have h := congrArg
        (fun k => (HomotopyCategory.quotient C (up ℤ)).map k)
        (adj.left_triangle_components K)
      rw [Functor.map_comp] at h
      exact h.trans ((HomotopyCategory.quotient C (up ℤ)).map_id _)
    right_triangle_components := by
      intro K
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
      dsimp [unit, counit]
      change
        (HomotopyCategory.quotient D (up ℤ)).map
              (adj.unit.app
                ((F.mapHomologicalComplex (up ℤ)).obj K)) ≫
            (HomotopyCategory.quotient D (up ℤ)).map
              ((F.mapHomologicalComplex (up ℤ)).map
                (adj.counit.app K)) =
          𝟙 ((HomotopyCategory.quotient D (up ℤ)).obj
            ((F.mapHomologicalComplex (up ℤ)).obj K))
      have h := congrArg
        (fun k => (HomotopyCategory.quotient D (up ℤ)).map k)
        (adj.right_triangle_components K)
      rw [Functor.map_comp] at h
      exact h.trans ((HomotopyCategory.quotient D (up ℤ)).map_id _) }

section Components

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C} [G.Additive] [F.Additive] (adj : G ⊣ F)

/-- The lifted complex unit is the original unit in each degree. -/
@[simp] theorem mapHomologicalComplexAdjunction_unit_app_f
    (c : ComplexShape ℤ) (K : HomologicalComplex D c) (i : ℤ) :
    ((mapHomologicalComplexAdjunction adj c).unit.app K).f i =
      adj.unit.app (K.X i) := rfl

/-- The lifted complex counit is the original counit in each degree. -/
@[simp] theorem mapHomologicalComplexAdjunction_counit_app_f
    (c : ComplexShape ℤ) (K : HomologicalComplex C c) (i : ℤ) :
    ((mapHomologicalComplexAdjunction adj c).counit.app K).f i =
      adj.counit.app (K.X i) := rfl

/-- The homotopy unit is the quotient of the lifted complex unit. -/
@[simp] theorem mapHomotopyCategoryAdjunction_unit_app
    (K : HomotopyCategory D (up ℤ)) :
    (mapHomotopyCategoryAdjunction adj).unit.app K =
      (HomotopyCategory.quotient D (up ℤ)).map
        ((mapHomologicalComplexAdjunction adj (up ℤ)).unit.app K.as) := rfl

/-- The homotopy counit is the quotient of the lifted complex counit. -/
@[simp] theorem mapHomotopyCategoryAdjunction_counit_app
    (K : HomotopyCategory C (up ℤ)) :
    (mapHomotopyCategoryAdjunction adj).counit.app K =
      (HomotopyCategory.quotient C (up ℤ)).map
        ((mapHomologicalComplexAdjunction adj (up ℤ)).counit.app K.as) := rfl

end Components

/-- The Hom-set equivalence on homotopy categories induced by an adjunction of additive functors.
-/
@[stacks 0DVC "hom-set equivalence on cochain homotopy categories"]
noncomputable def mapHomotopyCategoryCoreHomEquiv
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F) :
    Adjunction.CoreHomEquiv
      (G.mapHomotopyCategory (up ℤ))
      (F.mapHomotopyCategory (up ℤ)) := by
  exact {
    homEquiv := (mapHomotopyCategoryAdjunction adj).homEquiv
    homEquiv_naturality_left_symm :=
      (mapHomotopyCategoryAdjunction adj).homEquiv_naturality_left_symm
    homEquiv_naturality_right :=
      (mapHomotopyCategoryAdjunction adj).homEquiv_naturality_right }

namespace mapHomotopyCategoryCoreHomEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The forward hom-set map is induced by the ambient cochain-level adjunction. -/
@[simp, stacks 0DVC "forward computation of the homotopy-category hom-equivalence"]
theorem apply
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F)
    {L : HomotopyCategory D (up ℤ)} {K : HomotopyCategory C (up ℤ)}
    (f : (G.mapHomotopyCategory (up ℤ)).obj L ⟶ K) :
    (mapHomotopyCategoryCoreHomEquiv adj).homEquiv L K f =
      (HomotopyCategory.quotient D (up ℤ)).map
        (((mapHomologicalComplexAdjunction adj (up ℤ)).homEquiv L.as K.as) f.out) := by
  change (HomotopyCategory.quotient D (up ℤ)).map
        ((mapHomologicalComplexAdjunction adj (up ℤ)).unit.app L.as) ≫
      (F.mapHomotopyCategory (up ℤ)).map f =
    (HomotopyCategory.quotient D (up ℤ)).map
      ((mapHomologicalComplexAdjunction adj (up ℤ)).unit.app L.as ≫
        (F.mapHomologicalComplex (up ℤ)).map f.out)
  simp only [Functor.map_comp, ← Functor.mapHomotopyCategory_map,
    HomotopyCategory.quotient_map_out]

set_option backward.isDefEq.respectTransparency false in
/-- The inverse hom-set map is induced by the inverse ambient cochain-level adjunction. -/
@[simp, stacks 0DVC "inverse computation of the homotopy-category hom-equivalence"]
theorem symm_apply
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F)
    {L : HomotopyCategory D (up ℤ)} {K : HomotopyCategory C (up ℤ)}
    (g : L ⟶ (F.mapHomotopyCategory (up ℤ)).obj K) :
    ((mapHomotopyCategoryCoreHomEquiv adj).homEquiv L K).symm g =
      (HomotopyCategory.quotient C (up ℤ)).map
        (((mapHomologicalComplexAdjunction adj (up ℤ)).homEquiv L.as K.as).symm g.out) := by
  change (G.mapHomotopyCategory (up ℤ)).map g ≫
      (HomotopyCategory.quotient C (up ℤ)).map
        ((mapHomologicalComplexAdjunction adj (up ℤ)).counit.app K.as) =
    (HomotopyCategory.quotient C (up ℤ)).map
      ((G.mapHomologicalComplex (up ℤ)).map g.out ≫
        (mapHomologicalComplexAdjunction adj (up ℤ)).counit.app K.as)
  simp only [Functor.map_comp, ← Functor.mapHomotopyCategory_map,
    HomotopyCategory.quotient_map_out]

end mapHomotopyCategoryCoreHomEquiv

/-- The bounded-below homotopy-category adjunction induced by an adjunction of additive functors.

The construction is the canonical restriction of `mapHomotopyCategoryAdjunction` to the
`HomotopyCategory.plus` full subcategories.  Preservation of bounded-below objects is supplied by
the standard `Functor.Homotopy.Plus.mapsTo` API, so callers do not rebuild local instances. -/
@[stacks 014X "bounded-below homotopy adjunction"]
noncomputable def mapHomotopyCategoryPlusAdjunction
    {C : Type u₁} {D : Type u₂}
    [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {G : D ⥤ C}
    [G.Additive] [F.Additive]
    (adj : G ⊣ F) :
    G.mapHomotopyCategoryPlus ⊣ F.mapHomotopyCategoryPlus :=
  ObjectProperty.FullSubcategory.adjunction
    (G.mapHomotopyCategory (up ℤ)) (F.mapHomotopyCategory (up ℤ))
    (mapHomotopyCategoryAdjunction adj)
    (Functor.Homotopy.Plus.mapsTo G) (Functor.Homotopy.Plus.mapsTo F)

end CategoryTheory.Adjunction
