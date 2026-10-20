/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat.Relative
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism transport for relative K-flat homological complexes

Relative K-flatness depends only on the isomorphism class of the complex in the second variable
of the defining bifunctor.
@stack 06XZ
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w

namespace HomologicalComplex.IsKFlatFor

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
variable {I₁ : Type w₁} {I₂ : Type w₂} {J : Type w}
  {c₁ : ComplexShape I₁} {c₂ : ComplexShape I₂} {c : ComplexShape J}
  [TotalComplexShape c₁ c₂ c] [DecidableEq J]
variable {F : C₁ ⥤ C₂ ⥤ D} [F.PreservesZeroMorphisms]
  [∀ X : C₁, (F.obj X).PreservesZeroMorphisms]

/-- Relative K-flatness transports from the source to the target of an isomorphism of
homological complexes. -/
theorem of_iso {K L : HomologicalComplex C₂ c₂} (hK : K.IsKFlatFor F c₁ c) (e : K ≅ L) :
    L.IsKFlatFor F c₁ c := sorry

/-- Isomorphic homological complexes are simultaneously K-flat for a fixed bifunctor. -/
@[stacks 06XZ "isomorphism invariance of bifunctor-relative K-flatness"]
theorem iff_of_iso {K L : HomologicalComplex C₂ c₂} (e : K ≅ L) :
    K.IsKFlatFor F c₁ c ↔ L.IsKFlatFor F c₁ c := sorry

end HomologicalComplex.IsKFlatFor
