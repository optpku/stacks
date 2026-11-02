/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.RelativeDualizing
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Uniqueness

@[expose] public section

open CategoryTheory
open scoped TensorProduct

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- Derived extension along a field extension preserves canonical dualizing complexes of
finite-type algebras. -/
theorem baseChange_of_fieldExtension
    {k K A : Type u} [Field k] [Field K] [Algebra k K]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} (A ⊗[k] K)))]
    (CA : CanonicalClosedPresentation (A := A))
    (CAK : CanonicalClosedPresentation (A := A ⊗[k] K))
    (ω : DerivedCategory (ModuleCat.{u, u} A)) :
    let hA : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
    let hAK : IsNoetherianRing (A ⊗[k] K) :=
      Algebra.FiniteType.isNoetherianRing_tensor_left
    @DerivedCategory.IsCanonicalDualizingComplex A _ hA _ ω CA →
      @DerivedCategory.IsCanonicalDualizingComplex (A ⊗[k] K) _ hAK _
        ((ModuleCat.derivedExtensionOfScalars
          (algebraMap A (A ⊗[k] K))).obj ω) CAK := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
