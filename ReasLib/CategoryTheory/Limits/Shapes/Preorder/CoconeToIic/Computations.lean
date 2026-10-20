/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Shapes.Preorder.CoconeToIic.Basic
public import ReasLib.Order.Interval.Set.IioIic

/-!
# Computations for closed preorder cocone extensions

This file exposes object, morphism, and strict-restriction comparisons for
`Limits.Cocone.toIic`.
-/

@[expose] public section

universe u v w

namespace CategoryTheory.Limits.Cocone

open Category

variable {C : Type u} [Category.{v} C]
variable {I : Type w} [Preorder I]
variable {j : I} {F : Set.Iio j ⥤ C}

namespace toIic

/-- Below the cut, the extended object is the corresponding object of the
original strict-predecessor functor. -/
@[simp]
theorem objEq (c : Cocone F) (i : I) (hi : i < j) :
    c.toIic.obj ⟨i, hi.le⟩ = F.obj ⟨i, hi⟩ := sorry

/-- At an index not strictly below the cut, the extended object is the cocone
point. -/
@[simp]
theorem objEqPt (c : Cocone F) (i : I)
    (hi : ¬ i < j) (hij : i ≤ j) :
    c.toIic.obj ⟨i, hij⟩ = c.pt := sorry

/-- The extended object at the cut is the cocone point. -/
@[simp]
theorem cutEq (c : Cocone F) :
    c.toIic.obj ⟨j, le_rfl⟩ = c.pt := sorry

/-- The canonical comparison between the extended cut object and the cocone
point. -/
noncomputable def cutIso (c : Cocone F) :
    c.toIic.obj ⟨j, le_rfl⟩ ≅ c.pt :=
  objIsoPt c j (lt_irrefl j)

/-- Below the cut, an extended transition is the original transition
transported across the canonical object comparisons. -/
@[reassoc]
theorem mapOfLT (c : Cocone F) (i₁ i₂ : I)
    (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ < j) :
    c.toIic.map
        (homOfLE h₁₂ :
          (⟨i₁, (lt_of_le_of_lt h₁₂ h₂).le⟩ : Set.Iic j) ⟶ ⟨i₂, h₂.le⟩) =
      (objIso c i₁ (lt_of_le_of_lt h₁₂ h₂)).hom ≫
        F.map (homOfLE h₁₂) ≫ (objIso c i₂ h₂).inv := sorry

/-- A transition from a strict predecessor to a point equivalent to the cut
is the corresponding cocone leg, up to the canonical comparisons. -/
theorem mapToPoint (c : Cocone F) (i₁ i₂ : I)
    (h₁₂ : i₁ ≤ i₂) (h₂j : i₂ ≤ j) (h₁ : i₁ < j) (h₂ : ¬ i₂ < j) :
    c.toIic.map
        (homOfLE h₁₂ : (⟨i₁, h₁.le⟩ : Set.Iic j) ⟶ ⟨i₂, h₂j⟩) =
      (objIso c i₁ h₁).hom ≫ c.ι.app ⟨i₁, h₁⟩ ≫
        (objIsoPt c i₂ h₂).inv := sorry

/-- Between two points equivalent to the cut, the extended transition is the
identity of the cocone point transported across the canonical comparisons. -/
theorem mapPoint (c : Cocone F) (i₁ i₂ : I)
    (h₁₂ : i₁ ≤ i₂) (h₂j : i₂ ≤ j) (h₁ : ¬ i₁ < j) (h₂ : ¬ i₂ < j) :
    c.toIic.map
        (homOfLE h₁₂ :
          (⟨i₁, h₁₂.trans h₂j⟩ : Set.Iic j) ⟶ ⟨i₂, h₂j⟩) =
      (objIsoPt c i₁ h₁).hom ≫ (objIsoPt c i₂ h₂).inv := sorry

/-- The transition from a strict predecessor to the cut is the corresponding
cocone leg, up to the canonical object comparisons. -/
theorem mapToCut (c : Cocone F) (i : I) (hi : i < j) :
    c.toIic.map
        (homOfLE hi.le : (⟨i, hi.le⟩ : Set.Iic j) ⟶ ⟨j, le_rfl⟩) =
      (objIso c i hi).hom ≫ c.ι.app ⟨i, hi⟩ ≫ (cutIso c).inv := sorry

namespace objIso

/-- Naturality of the strict-predecessor object comparisons. -/
@[reassoc]
theorem homNaturality (c : Cocone F)
    (i₁ i₂ : I) (h₁₂ : i₁ ≤ i₂) (h₂ : i₂ < j) :
    c.toIic.map
          (homOfLE h₁₂ :
            (⟨i₁, (lt_of_le_of_lt h₁₂ h₂).le⟩ : Set.Iic j) ⟶ ⟨i₂, h₂.le⟩) ≫
        (toIic.objIso c i₂ h₂).hom =
      (toIic.objIso c i₁ (lt_of_le_of_lt h₁₂ h₂)).hom ≫
        F.map (homOfLE h₁₂) := sorry

end objIso

/-- The restriction of the extended functor to strict predecessors. -/
noncomputable def restriction (c : Cocone F) : Set.Iio j ⥤ C :=
  (Set.iioToIic j).toFunctor ⋙ c.toIic

namespace restriction

/-- Object formula for the strict restriction. -/
@[simp]
theorem obj (c : Cocone F) (i : Set.Iio j) :
    (restriction c).obj i = c.toIic.obj ⟨i.1, i.2.le⟩ := sorry

/-- Morphism formula for the strict restriction. -/
@[simp]
theorem map (c : Cocone F)
    {i₁ i₂ : Set.Iio j} (f : i₁ ⟶ i₂) :
    (restriction c).map f =
      c.toIic.map
        (homOfLE (leOfHom f) :
          (⟨i₁.1, i₁.2.le⟩ : Set.Iic j) ⟶ ⟨i₂.1, i₂.2.le⟩) := sorry

end restriction

namespace restrictionIso

/-- Naturality of the comparison between the strict restriction and the
original functor. -/
theorem naturality (c : Cocone F)
    {i₁ i₂ : Set.Iio j} (f : i₁ ⟶ i₂) :
    (restriction c).map f ≫ (toIic.objIso c i₂.1 i₂.2).hom =
      (toIic.objIso c i₁.1 i₁.2).hom ≫ F.map f := sorry

end restrictionIso

/-- The strict restriction of a closed cocone extension is canonically
isomorphic to the original functor. -/
noncomputable def restrictionIso (c : Cocone F) :
    restriction c ≅ F :=
  NatIso.ofComponents (fun i => objIso c i.1 i.2)
    (fun f => restrictionIso.naturality c f)

namespace restrictionIso

/-- Component formula for the strict-restriction comparison. -/
@[simp]
theorem homApp (c : Cocone F) (i : Set.Iio j) :
    (restrictionIso c).hom.app i = (toIic.objIso c i.1 i.2).hom := sorry

end restrictionIso

end toIic

end CategoryTheory.Limits.Cocone
