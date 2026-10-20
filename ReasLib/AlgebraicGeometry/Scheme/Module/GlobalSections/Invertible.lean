module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.PicardGroup
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic

/-!
# Global sections of invertible scheme modules

This module records descent of invertibility and of the evaluation pairing from
a trivial faithfully flat affine base change.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.GlobalSections

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
variable (L : X.Modules)

/-- An invertible scheme module with trivial faithfully flat affine base change has invertible
global sections. -/
@[stacks 0CDX]
theorem invertible_of_trivial_faithfullyFlat_baseChange
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier] [Invertible L]
    (hff : (algebraMap A B).FaithfullyFlat)
    (htriv : RingedSpace.IsTrivial (AffineBaseChange.baseChange A B f L)) :
    Module.Invertible (Γ(X, ⊤)) Γ(L, ⊤) := sorry

/-- The global sections of the internal-Hom inverse of an invertible scheme module are
invertible when the module becomes trivial after a faithfully flat affine base change. -/
@[stacks 0CDX]
theorem inverse_invertible_of_trivial_faithfullyFlat_baseChange
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier] [Invertible L]
    (hff : (algebraMap A B).FaithfullyFlat)
    (htriv : RingedSpace.IsTrivial (AffineBaseChange.baseChange A B f L)) :
    Module.Invertible (Γ(X, ⊤))
      Γ((ihom L).obj (SheafOfModules.unit X.ringCatSheaf : X.Modules), ⊤) := sorry

/-- The global-sections evaluation pairing of an invertible scheme module is bijective when the
module becomes trivial after a faithfully flat affine base change. -/
@[stacks 0CDX]
theorem evaluation_bijective_of_trivial_faithfullyFlat_baseChange
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier] [Invertible L]
    (hff : (algebraMap A B).FaithfullyFlat)
    (htriv : RingedSpace.IsTrivial (AffineBaseChange.baseChange A B f L)) :
    Function.Bijective (RingedSpace.GlobalSections.evaluationLinearMap L) := sorry

end AlgebraicGeometry.Scheme.Modules.GlobalSections
