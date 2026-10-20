/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Logic.Unique
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Basic

/-!
# Predeformation functors

A functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a predeformation functor when
its value at `ArtinianLocalAlgCat.residue Λ k` is a singleton.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- A functor `F : ArtinianLocalAlgCat Λ k ⥤ Type v` is a predeformation functor if
`F.obj (ArtinianLocalAlgCat.residue Λ k)` is a singleton. -/
class IsPredeformationFunctor (F : ArtinianLocalAlgCat Λ k ⥤ Type v) : Prop where
  /-- The value at the residue field is a singleton. -/
  unique_residue : Nonempty (Unique (F.obj (ArtinianLocalAlgCat.residue Λ k)))

/-- A functor to types with a unique value at the residue field is a predeformation functor. -/
instance instIsPredeformationFunctor
    {F : ArtinianLocalAlgCat Λ k ⥤ Type v}
    [Unique (F.obj (ArtinianLocalAlgCat.residue Λ k))] :
    IsPredeformationFunctor F :=
  ⟨⟨inferInstance⟩⟩

/-- A functor is a predeformation functor iff its value at the residue field is a singleton. -/
theorem isPredeformationFunctor_iff (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    IsPredeformationFunctor F ↔
      Nonempty (Unique (F.obj (ArtinianLocalAlgCat.residue Λ k))) := sorry

/-- A predeformation category has a cofibered-in-groupoids opposite projection. -/
instance isFiberedInGroupoids_op
    {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] :
    IsFibered.InGroupoids p.op := sorry

/-- A functor is predeformation exactly when its category-of-elements projection is a
predeformation category. -/
theorem isPredeformationFunctor_iff_isPredeformationCategory
    (F : ArtinianLocalAlgCat Λ k ⥤ Type v) :
    IsPredeformationFunctor F ↔ IsPredeformationCategory (CategoryOfElements.π F) := sorry

/-- The category of elements of a predeformation functor is a predeformation category. -/
instance instIsPredeformationCategory_ofTypeValued
    {G : ArtinianLocalAlgCat Λ k ⥤ Type v} [IsPredeformationFunctor G] :
    IsPredeformationCategory (CategoryOfElements.π G) :=
  (isPredeformationFunctor_iff_isPredeformationCategory G).mp inferInstance

/-- The fiberwise isomorphism-class presheaf of a predeformation category is a predeformation
functor. -/
instance fiberIsoClassPresheaf_isPredeformationFunctor
    {F : Type v} [Category.{w} F] (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsPredeformationCategory p] :
    IsPredeformationFunctor
      (opOp (ArtinianLocalAlgCat Λ k) ⋙ fiberIsoClassPresheaf p.op) := sorry

end CategoryTheory.Functor
