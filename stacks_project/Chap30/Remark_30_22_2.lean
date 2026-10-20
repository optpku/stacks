/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.FiniteProjectiveModel
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

open AlgebraicGeometry.Scheme.Modules in
/- Remark 30.22.2. A bounded complex of finite projective base modules computes the
cohomology of every affine base change, functorially in the base algebra.
Flatness of the coherent sheaf over the base is essential; see Hartshorne. -/
@[stacks 07VL] #check
  (AlgebraicGeometry.Scheme.Modules.exists_boundedFiniteProjective_cohomology_extendScalars :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (hflat : flatOver ℱ f),
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
            CochainComplex.extendScalarsHomologyMap M g (i : ℤ) ((φ B i).hom x))
