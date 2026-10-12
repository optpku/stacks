/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.Relative
public import ReasLib.Algebra.Homology.HomologicalComplex.KFlat.Relative.Isomorphism
import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphism Transport for Relative K-Flat Complexes

This file specializes the shape-general isomorphism API to cochain complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u₁ v₁ u₂ v₂ u₃ v₃

namespace CochainComplex

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  [HasZeroMorphisms C₁] [HasZeroMorphisms C₂] [Preadditive D]
variable {F : C₁ ⥤ C₂ ⥤ D} [F.PreservesZeroMorphisms]
  [∀ X : C₁, (F.obj X).PreservesZeroMorphisms]

namespace IsKFlatFor

/-- Relative K-flatness transports from the source to the target of an isomorphism of cochain
complexes. -/
theorem of_iso {K L : CochainComplex C₂ ℤ} (hK : K.IsKFlatFor F) (e : K ≅ L) :
    L.IsKFlatFor F := sorry

/-- Isomorphic cochain complexes are simultaneously K-flat for a fixed bifunctor. -/
theorem iff_of_iso {K L : CochainComplex C₂ ℤ} (e : K ≅ L) :
    K.IsKFlatFor F ↔ L.IsKFlatFor F := sorry

end IsKFlatFor

end CochainComplex
