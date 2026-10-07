module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.RingTheory.Flat.Basic
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import ReasLib.CategoryTheory.Monoidal.Flat

/-!
# Flat presheaves of modules

This file specializes monoidal flatness to module presheaves and owns flat morphisms of
commutative-ring-valued presheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory
open PresheafOfModules.Monoidal

noncomputable section

universe u v

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]

/-- Flatness of a module presheaf, specialized from the monoidal-category owner. -/
@[stacks 03ER "presheaf modules"]
abbrev IsFlat {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) : Prop :=
  CategoryTheory.MonoidalCategory.IsFlat ℱ

namespace IsFlat

/-- The exactness field of the canonical monoidal flatness owner. -/
theorem exact_tensor {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {ℱ : PresheafOfModules (ringPresheaf 𝒪)} [IsFlat ℱ] :
    exactFunctor
      (PresheafOfModules (ringPresheaf 𝒪))
      (PresheafOfModules (ringPresheaf 𝒪))
      (tensorRight ℱ) := sorry

/-- The tensor-right functor of a flat presheaf of modules is exact. -/
theorem exactTensor {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    (ℱ : PresheafOfModules (ringPresheaf 𝒪)) [IsFlat ℱ] :
    exactFunctor
      (PresheafOfModules (ringPresheaf 𝒪))
      (PresheafOfModules (ringPresheaf 𝒪))
      (tensorRight ℱ) := sorry

end IsFlat

/-- A morphism of commutative-ring-valued presheaves is flat when its target, restricted to a
module over the source, is flat. -/
def IsFlatHom {𝒪 𝒪' : Cᵒᵖ ⥤ CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') : Prop :=
  IsFlat ((PresheafOfModules.restrictScalars (presheafStructureMap α)).obj
    (PresheafOfModules.unit (ringPresheaf 𝒪')))

/-- Presheaf flatness of a ring morphism is flatness of the restricted target unit module. -/
theorem isFlatHom_iff {𝒪 𝒪' : Cᵒᵖ ⥤ CommRingCat.{max u v}} (α : 𝒪 ⟶ 𝒪') :
    IsFlatHom α ↔
      IsFlat ((PresheafOfModules.restrictScalars (presheafStructureMap α)).obj
        (PresheafOfModules.unit (ringPresheaf 𝒪'))) := sorry

/-- The structure presheaf, regarded as a module over itself, is flat. -/
@[instance]
theorem unit_isFlat (𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    IsFlat (PresheafOfModules.unit (ringPresheaf 𝒪)) := sorry

/-- Objectwise flat sections make a module presheaf flat. -/
@[stacks 03ES]
theorem isFlat_of_flat_obj
    {𝒪 : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    (ℱ : PresheafOfModules (ringPresheaf 𝒪))
    (hflat : ∀ U : C, Module.Flat (𝒪.obj (op U)) (ℱ.obj (op U))) :
    IsFlat ℱ := sorry

end PresheafOfModules
