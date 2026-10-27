/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.GlobalSections.Obstruction
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.FiniteProjectiveModel
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor

/-! # Dual obstruction complexes for global sections -/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.GlobalSections

variable {Λ : Type u} [CommRing Λ]

/-- The dual-obstruction complex `K = (N ⊗_Λ A)[-1]`, obtained by underived scalar
extension of `N` from `Λ` to `A` followed by a shift of `-1`. -/
def dualObstructionComplex (A : Type u) [CommRing A] [Algebra Λ A]
    (N : CochainComplex (ModuleCat Λ) ℤ) :
    CochainComplex (ModuleCat A) ℤ :=
  (shiftFunctor (CochainComplex (ModuleCat A) ℤ) (-1 : ℤ)).obj
    (((ModuleCat.extendScalars (algebraMap Λ A)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N)

/-- Scalar extension and a shift of `-1` preserve bounded finite-projective complexes. -/
instance dualObstructionComplex.instIsBoundedFiniteProjective
    {A : Type u} [CommRing A] [Algebra Λ A]
    (N : CochainComplex (ModuleCat Λ) ℤ) [N.IsBoundedFiniteProjective] :
    (dualObstructionComplex A N).IsBoundedFiniteProjective := sorry

/-- A coherent module flat over a proper morphism to a Noetherian affine scheme admits
one bounded finite-projective complex computing cohomology universally, compatibly with
algebra homomorphisms and with vanishing negative homology after scalar extension.
For every base algebra, its obstruction functor is naturally isomorphic both to degree-one
ordinary coefficient homology of that complex and to degree-two derived coefficient homology
of its scalar extension shifted by `-1`. -/
theorem exists_dualObstructionModel
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] {W : Scheme.{u}}
    (w : W ⟶ Spec (CommRingCat.of Λ)) [IsProper w]
    (F : W.Modules) [F.IsCoherent] (hflat : Scheme.Modules.flatOver F w) :
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
        IsIsomorphic (obstructionModule w F A)
          (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ) ⋙
            DerivedCategory.DerivedTensor.Left.complexFunctor NA ⋙
            HomologicalComplex.homologyFunctor (ModuleCat A) (ComplexShape.up ℤ) (1 : ℤ)) ∧
        IsIsomorphic (obstructionModule w F A)
          (ModuleCat.single0Functor ⋙
            DerivedCategory.DerivedTensor.Bifunctor.leftFunctor
              (DerivedCategory.Q.obj (dualObstructionComplex A N)) ⋙
            DerivedCategory.homologyFunctor (ModuleCat A) (2 : ℤ)) := sorry

end AlgebraicGeometry.GroupoidsOver.GlobalSections
