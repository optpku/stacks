/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.GlobalSections.DualObstruction
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Example 98.24.1. A universal finite-projective cohomology model computes the
obstruction functor by degree-one ordinary tensor homology and, after shifting
its scalar extension by `-1`, by degree-two derived tensor homology. -/
@[stacks 07YW] #check
  (AlgebraicGeometry.GroupoidsOver.GlobalSections.exists_dualObstructionModel :
    ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] {W : Scheme.{u}}
    (w : W ⟶ Spec (CommRingCat.of Λ)) [IsProper w]
    (F : W.Modules) [F.IsCoherent] (hflat : Scheme.Modules.flatOver F w),
    ∃ (N : CochainComplex (ModuleCat Λ) ℤ),
      CochainComplex.IsBoundedFiniteProjective N ∧
      (∀ (B : Type u) [CommRing B] [Algebra Λ B] (j : ℤ), j < 0 →
        Limits.IsZero ((((ModuleCat.extendScalars (algebraMap Λ B)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N).homology j)) ∧
      (∃ (φ : ∀ (B : Type u) [CommRing B] [Algebra Λ B] (i : ℕ),
        Scheme.Hom.cohomology (Scheme.AffineBaseChange.toBase Λ B w)
            (Scheme.Modules.AffineBaseChange.baseChange Λ B w F) i ≅
          (((ModuleCat.extendScalars (algebraMap Λ B)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N).homology (i : ℤ)),
        ∀ (B C : Type u) [CommRing B] [CommRing C] [Algebra Λ B] [Algebra Λ C]
          (g : B →ₐ[Λ] C) (i : ℕ)
          (x : Scheme.Hom.cohomology (Scheme.AffineBaseChange.toBase Λ B w)
            (Scheme.Modules.AffineBaseChange.baseChange Λ B w F) i),
          (φ C i).hom (Scheme.Modules.affineBaseChangeCohomologyMap w F g i x) =
            CochainComplex.extendScalarsHomologyMap N g (i : ℤ) ((φ B i).hom x)) ∧
      ∀ (A : Type u) [CommRing A] [Algebra Λ A],
        let NA := ((ModuleCat.extendScalars (algebraMap Λ A)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj N
        IsIsomorphic (AlgebraicGeometry.GroupoidsOver.GlobalSections.obstructionModule w F A)
          (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ) ⋙
            DerivedCategory.DerivedTensor.Left.complexFunctor NA ⋙
            HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) (1 : ℤ)) ∧
        IsIsomorphic (AlgebraicGeometry.GroupoidsOver.GlobalSections.obstructionModule w F A)
          (ModuleCat.single0Functor ⋙
            DerivedCategory.DerivedTensor.Bifunctor.leftFunctor
              (DerivedCategory.Q.obj (AlgebraicGeometry.GroupoidsOver.GlobalSections.dualObstructionComplex A N)) ⋙
            DerivedCategory.homologyFunctor (ModuleCat A) (2 : ℤ)))
