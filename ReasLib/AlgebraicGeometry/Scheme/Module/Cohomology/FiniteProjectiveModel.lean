/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.FiniteProjective
public import ReasLib.Algebra.Homology.CochainComplex.ScalarExtensionHomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineBaseChangeMap
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Finite projective models for cohomology over an affine base -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- A coherent module flat over a proper morphism to a Noetherian affine scheme has a
bounded finite-projective complex computing its cohomology after every algebra base change.
One family of module isomorphisms intertwines geometric pullback with coefficient change,
and the scalar-extended complex has no negative-degree homology. -/
theorem exists_boundedFiniteProjective_cohomology_extendScalars
    {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (hflat : flatOver ℱ f) :
    ∃ (M : CochainComplex (ModuleCat A) ℤ),
      CochainComplex.IsBoundedFiniteProjective M ∧
      (∀ (B : Type u) [CommRing B] [Algebra A B] (j : ℤ), j < 0 →
        Limits.IsZero ((((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj M).homology j)) ∧
      ∃ (φ : ∀ (B : Type u) [CommRing B] [Algebra A B] (i : ℕ),
        Scheme.Hom.cohomology (Scheme.AffineBaseChange.toBase A B f)
            (AffineBaseChange.baseChange A B f ℱ) i ≅
          (((ModuleCat.extendScalars (algebraMap A B)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj M).homology (i : ℤ)),
        ∀ (B C : Type u) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
          (g : B →ₐ[A] C) (i : ℕ)
          (x : Scheme.Hom.cohomology (Scheme.AffineBaseChange.toBase A B f)
            (AffineBaseChange.baseChange A B f ℱ) i),
          (φ C i).hom (affineBaseChangeCohomologyMap f ℱ g i x) =
            CochainComplex.extendScalarsHomologyMap M g (i : ℤ) ((φ B i).hom x) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
