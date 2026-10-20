/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Definition

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y Z : LocallyRingedSpace.{u}} (p : Y ⟶ X) (q : Z ⟶ X)

/-- If the canonical inverse-image structure-sheaf map of `p : Y ⟶ X` is an
isomorphism, forgetting sheaf maps gives a bijection from locally ringed-space
morphisms over `X` into `Y` to continuous maps over the underlying space of `X`. -/
theorem overPost_forgetToTop_map_bijective
    (h_inverseImage : IsIso (RingedSpace.Hom.inverseImageStructureSheafHomComm p.toShHom)) :
    Function.Bijective fun φ : Over.mk q ⟶ Over.mk p ↦ (Over.post forgetToTop).map φ := sorry

/-- When the canonical inverse-image structure-sheaf map of `p : Y ⟶ X` is an
isomorphism, every continuous map over `X` into `Y` lifts uniquely to a morphism
of locally ringed spaces over `X`. -/
theorem existsUnique_hom_of_base
    (h_inverseImage : IsIso (RingedSpace.Hom.inverseImageStructureSheafHomComm p.toShHom))
    (f : forgetToTop.obj Z ⟶ forgetToTop.obj Y)
    (hf : f ≫ forgetToTop.map p = forgetToTop.map q) :
    ∃! φ : Z ⟶ Y, forgetToTop.map φ = f ∧ φ ≫ p = q := sorry

end AlgebraicGeometry.LocallyRingedSpace
