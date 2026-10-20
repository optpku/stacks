/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Algebra.Homology.LocalCohomology
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.Ext
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Closed
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.RHom
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Torsion
public import ReasLib.Algebra.Module.Injective.Hull

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/-- For a Noetherian local ring, the zeroth homology of the maximal-ideal local
cohomology of a normalized dualizing complex admits an injective-hull embedding
of the residue field. -/
theorem localCohomologyH0IsInjectiveHull
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓZ : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓZ) :
    let K := (RΓZ.obj ω).obj
    let E := (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj K
    ∃ (_ : Module.Injective A E) (ι : IsLocalRing.ResidueField A →ₗ[A] E),
      ι.IsInjectiveHull := sorry

/-- For a Noetherian local ring, maximal-ideal local cohomology of a normalized
dualizing complex is isomorphic to its zeroth homology concentrated in degree zero. -/
theorem localCohomologyIsoSingleH0
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓZ : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓZ) :
    let K := (RΓZ.obj ω).obj
    let E := (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj K
    Nonempty (K ≅ ModuleCat.single0 E) := sorry

/-- A prime belongs to the support of a bounded initial family of Ext modules exactly when the
localized depth condition with the residue-dimension term holds. -/
theorem mem_support_extUpTo_iff
    (A M : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (comparison :
      CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison (A := A))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsNormalizedDualizingComplex comparison.closed)
    (i : ℕ) (p : PrimeSpectrum A) :
    (∃ j : ℕ, j ≤ i ∧
      p ∈ Module.support A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(j : ℤ))).obj
          ((MonoidalClosed.ihomOf comparison.closed
            (ModuleCat.single0 (ModuleCat.of A M))).obj ω))) ↔
      (.some (moduleDepth (Localization.AtPrime p.asIdeal)
        (LocalizedModule.AtPrime p.asIdeal M)) : WithBot ℕ∞) +
          ringKrullDim (A ⧸ p.asIdeal) ≤ .some (i : ℕ∞) := sorry

/-- The annihilator of each Ext module of a finite module into a normalized dualizing complex
equals the annihilator of the corresponding maximal-ideal local cohomology module. -/
theorem annihilator_ext_eq_localCohomology
    (A M : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (comparison :
      CategoryTheory.DerivedCategory.InternalHom.RHom.ClosedComparison (A := A))
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : ω.IsNormalizedDualizingComplex comparison.closed) (i : ℕ) :
    Module.annihilator A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-(i : ℤ))).obj
        ((MonoidalClosed.ihomOf comparison.closed
          (ModuleCat.single0 (ModuleCat.of A M))).obj ω)) =
      Module.annihilator A
        ((localCohomology (IsLocalRing.maximalIdeal A) i).obj (ModuleCat.of A M)) := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
