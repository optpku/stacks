/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap98.Example_98_22_3_Obstruction
public import stacks_project.Chap30.Remark_30_22_2
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dual obstruction complexes from global-sections cohomology

When `w : W ⟶ Spec(Λ)` is proper and `F` is coherent and flat over `S`, a bounded
finite-projective model of `RΓ(W, F)` identifies the obstruction modules `O_x(M)`
with homology of a shifted scalar extension.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry.Scheme.Modules
open scoped AlgebraicGeometry

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

/-- `dualObstructionComplex A N` is the `-1`-shift of the underived scalar extension of `N`. -/
theorem dualObstructionComplex_eq {A : Type u} [CommRing A] [Algebra Λ A]
    (N : CochainComplex (ModuleCat Λ) ℤ) :
    dualObstructionComplex A N =
      (shiftFunctor (CochainComplex (ModuleCat A) ℤ) (-1 : ℤ)).obj
        (((ModuleCat.extendScalars (algebraMap Λ A)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj N) :=
  sorry

/-- Scalar extension and a shift of `-1` preserve bounded finite-projective complexes. -/
instance dualObstructionComplex.instIsBoundedFiniteProjective
    {A : Type u} [CommRing A] [Algebra Λ A]
    (N : CochainComplex (ModuleCat Λ) ℤ) [N.IsBoundedFiniteProjective] :
    (dualObstructionComplex A N).IsBoundedFiniteProjective :=
  sorry

variable [IsNoetherianRing Λ]
variable {W : Scheme.{u}} (w : W ⟶ S Λ) (F : W.Modules)

/-- Example 98.24.1 (1): in the setup of Example 98.22.3, if `w` is proper and `F` is
coherent, Remark 30.22.2 supplies a finite complex of finite projective `Λ`-modules
which universally computes the cohomology of `F`. -/
@[stacks 07YW]
theorem exists_boundedFiniteProjective_universallyComputes
    [IsProper w]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived Λ w]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived Λ w]
    [AffineBaseModuleDerivedAdjunction.HasPair Λ w]
    [F.IsCoherent] (hflat : flatOver F w) :
    ∃ (N : CochainComplex (ModuleCat Λ) ℤ),
      CochainComplex.IsBoundedFiniteProjective N ∧
        ∀ (A' : Type u) [CommRing A'] [Algebra Λ A']
          [AffineBaseModuleDerivedAdjunction.HasLeftDerived A'
            (Scheme.AffineBaseChange.toBase Λ A' w)]
          [AffineBaseModuleDerivedAdjunction.HasRightDerived A'
            (Scheme.AffineBaseChange.toBase Λ A' w)]
          [AffineBaseModuleDerivedAdjunction.HasPair A'
            (Scheme.AffineBaseChange.toBase Λ A' w)]
          [AffineBaseChangeDerivedCompatibility.HasScalarExtension Λ A']
          [AffineBaseChangeDerivedCompatibility.HasPullback Λ A' w]
          [AffineBaseChangeDerivedCompatibility.SourceRoute Λ A' w]
          [AffineBaseChangeDerivedCompatibility.TargetRoute Λ A' w]
          (i : ℤ),
          IsIsomorphic
            ((DerivedCategory.homologyFunctor (ModuleCat A') i).obj
              (affineBaseChangedModuleDerivedGlobalSections Λ A' w F))
            ((((ModuleCat.extendScalars (algebraMap Λ A')).mapHomologicalComplex
                (ComplexShape.up ℤ)).obj N).homology i) :=
  sorry

/-- Example 98.24.1 (2): the obstruction modules of Example 98.22.3 satisfy
`O_x(M) ≅ H^1((N ⊗_Λ A) ⊗_A M)` as `A`-modules. -/
@[stacks 07YW]
theorem obstructionModule_iso_scalarExtensionHomology
    [IsProper w] [F.IsCoherent]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived Λ w]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived Λ w]
    [AffineBaseModuleDerivedAdjunction.HasPair Λ w]
    (hflat : flatOver F w)
    (N : CochainComplex (ModuleCat Λ) ℤ)
    [N.IsBoundedFiniteProjective]
    (e : affineBaseModuleDerivedGlobalSections Λ w F ≅ DerivedCategory.Q.obj N)
    {A : Type u} [CommRing A] [Algebra Λ A] (M : ModuleCat A) :
    IsIsomorphic ((obstructionModule w F A).obj M)
      ((((tensorRight M).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (((ModuleCat.extendScalars (algebraMap Λ A)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj N)).homology (1 : ℤ)) :=
  sorry

/-- Example 98.24.1 (3): with `K = dualObstructionComplex A N`, the obstruction modules
satisfy `O_x(M) ≅ H^2(K ⊗^L_A M)`. -/
@[stacks 07YW]
theorem obstructionModule_iso_dualComplexHomology
    [IsProper w] [F.IsCoherent]
    [AffineBaseModuleDerivedAdjunction.HasLeftDerived Λ w]
    [AffineBaseModuleDerivedAdjunction.HasRightDerived Λ w]
    [AffineBaseModuleDerivedAdjunction.HasPair Λ w]
    (hflat : flatOver F w)
    (N : CochainComplex (ModuleCat Λ) ℤ)
    [N.IsBoundedFiniteProjective]
    (e : affineBaseModuleDerivedGlobalSections Λ w F ≅ DerivedCategory.Q.obj N)
    {A : Type u} [CommRing A] [Algebra Λ A] (M : ModuleCat A) :
    IsIsomorphic ((obstructionModule w F A).obj M)
      ((DerivedCategory.homologyFunctor (ModuleCat A) (2 : ℤ)).obj
        ((DerivedCategory.derivedTensorProduct (ModuleCat.single0 M)).obj
          (DerivedCategory.Q.obj (dualObstructionComplex A N)))) :=
  sorry

end AlgebraicGeometry.GroupoidsOver.GlobalSections
