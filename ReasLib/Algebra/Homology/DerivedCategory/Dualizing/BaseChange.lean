/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.FaithfullyFlat
public import ReasLib.RingTheory.RingHom.Syntomic.LocalCompleteIntersection
public import ReasLib.RingTheory.Gorenstein.Ring

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IsDualizingComplex

/-- For a homomorphism of Noetherian commutative rings satisfying one of the
syntomic-surjective, faithfully flat local complete-intersection, or faithfully
flat finite-type Gorenstein-fibre conditions, canonical dualizing complexes are
preserved and reflected by derived extension of scalars. -/
theorem iff_derivedExtensionOfScalars
    {A B : Type u} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
    (φ : A →+* B)
    (hφ :
      (φ.Syntomic ∧ Function.Surjective (PrimeSpectrum.comap φ)) ∨
        (φ.FaithfullyFlat ∧ φ.IsLocalCompleteIntersection) ∨
        (φ.FaithfullyFlat ∧ φ.FiniteType ∧
          ∀ p : PrimeSpectrum A, IsGorensteinRing (φ.Fiber p.asIdeal)))
    (CA : CanonicalClosedPresentation (A := A))
    (CB : CanonicalClosedPresentation (A := B))
    (K : DerivedCategory (ModuleCat.{u} A)) :
    K.IsCanonicalDualizingComplex CA ↔
      ((ModuleCat.derivedExtensionOfScalars φ).obj K).IsCanonicalDualizingComplex CB := sorry

end CategoryTheory.DerivedCategory.IsDualizingComplex
