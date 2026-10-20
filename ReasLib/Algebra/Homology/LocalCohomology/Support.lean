/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ClosedSubset.SectionsWithSupport
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace localCohomology

/-- Global sections of module sheaves on `Spec A` supported on `V(I)`,
viewed as `A`-modules through the canonical isomorphism `A ≃ Γ(Spec A, ⊤)`. -/
noncomputable abbrev sectionsWithSupport {A : Type u} [CommRing A] (I : Ideal A) :
    (Spec (CommRingCat.of A)).Modules ⥤ ModuleCat A :=
  let X := Spec (CommRingCat.of A)
  let Z : Closeds (PrimeSpectrum A) :=
    ⟨PrimeSpectrum.zeroLocus (R := A) (I : Set A),
      PrimeSpectrum.isClosed_zeroLocus (R := A) (I : Set A)⟩
  SheafOfModules.ClosedSubset.SectionsWithSupport.functor X.ringCatSheaf Z ⋙
    SheafOfModules.ClosedSubset.pushforward X.ringCatSheaf Z ⋙
    SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- Global sections supported on `V(I)`, viewed as `A`-modules, form an additive functor. -/
instance sectionsWithSupport_additive {A : Type u} [CommRing A] (I : Ideal A) :
    (sectionsWithSupport I).Additive := sorry

/-- Degree-`i` geometric cohomology supported on `V(I)` of the associated
module sheaf on `Spec A`, obtained by deriving supported global sections on
the category of all module sheaves before applying the affine tilde functor. -/
noncomputable abbrev withSupport {A : Type u} [CommRing A] (I : Ideal A) (i : ℕ) :
    ModuleCat A ⥤ ModuleCat A :=
  tilde.functor (CommRingCat.of A) ⋙ (sectionsWithSupport I).rightDerived i

end localCohomology
