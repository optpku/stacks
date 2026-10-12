/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.CommRing
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Additivity of tensor products of module presheaves

The pointwise tensor product of module presheaves is compatible with the preadditive structure.
Registering this fact at the tensor layer lets homological constructions infer preservation of
zero morphisms without installing local instances in every exactness argument.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace PresheafOfModules

variable {C : Type u} [Category.{v} C]
variable {O : Cᵒᵖ ⥤ CommRingCat.{max u v}}

/-- The pointwise tensor product of module presheaves is additive in both variables. -/
instance monoidalPreadditive :
    MonoidalPreadditive (PresheafOfModules (ringPresheaf O)) := sorry

end PresheafOfModules
