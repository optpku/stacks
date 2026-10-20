/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.InternalHom
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.LocalCohomology
public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Basic

@[expose] public section

open CategoryTheory
open DerivedCategory
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex

/-- For a Noetherian local ring with normalized dualizing complex `ω` and an
injective hull `E` of the residue field, derived completion of `RHom_A(K, ω)`
is isomorphic to `RHom_A(RΓ_Z(K), E[0])` for every `K` in `D(A)`. -/
theorem localDuality
    (A E : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup E] [Module A E] [Module.Injective A E]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
    (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤
      IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓZ : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓZ)
    (K : DerivedCategory (ModuleCat A)) :
    Nonempty
      (derivedCompletionOf (IsLocalRing.maximalIdeal A)
          (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A))
          (InternalHom.RHom.obj K ω) ≅
        InternalHom.RHom.obj (RΓZ.obj K).obj
          (ModuleCat.single0 (ModuleCat.of A E))) := sorry

/-- For a Noetherian local ring with normalized dualizing complex, the completed Ext modules of
coherent derived objects are canonically dual to their local cohomology modules. -/
theorem completedExtIsoLocalCohomologyDual
    (A E : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [AddCommGroup E] [Module A E] [Module.Injective A E]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [BraidedCategory (DerivedCategory (ModuleCat.{u} A))]
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (ω : DerivedCategory (ModuleCat.{u} A)) (hω : ω.IsNormalizedDualizingComplex H)
    (ι : IsLocalRing.ResidueField A →ₗ[A] E) (hι : ι.IsInjectiveHull)
    (RΓZ : DerivedCategory (ModuleCat A) ⥤
      IdealPowerTorsion (IsLocalRing.maximalIdeal A))
    (hRΓZ : IdealPowerTorsion.inclusion (IsLocalRing.maximalIdeal A) ⊣ RΓZ)
    (K : D[ModuleCat.isFG A]) (i : ℤ) :
    IsIsomorphic
      (ModuleCat.of A
        (AdicCompletion (IsLocalRing.maximalIdeal A)
          ((homologyFunctor (ModuleCat A) (-i)).obj
            (InternalHom.RHom.obj K.obj ω))))
      (ModuleCat.of A
        (((homologyFunctor (ModuleCat A) i).obj (RΓZ.obj K.obj).obj) →ₗ[A] E)) := sorry

end CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex
