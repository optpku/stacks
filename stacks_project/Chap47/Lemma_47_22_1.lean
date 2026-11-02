/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.FlatExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 47.22.1: a flat local homomorphism of Noetherian local rings that maps the source
maximal ideal onto the target maximal ideal carries a normalized dualizing complex to a normalized
dualizing complex by derived extension of scalars. -/
@[stacks 0AWD] #check
  (CategoryTheory.DerivedCategory.IsNormalizedDualizingComplex.baseChange_of_flat_of_mapsMaximalIdeal :
    ∀ {A B : Type u} [CommRing A] [CommRing B]
      [IsNoetherianRing A] [IsNoetherianRing B]
      [IsLocalRing A] [IsLocalRing B]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
      [MonoidalCategory (DerivedCategory (ModuleCat.{u} B))]
      (f : A →+* B) [IsLocalHom f] (hflat : f.Flat) (hmax : f.MapsMaximalIdeal)
      (CA : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := A))
      (CB : CategoryTheory.DerivedCategory.CanonicalClosedPresentation (A := B))
      (ω : DerivedCategory (ModuleCat.{u} A)),
      ω.IsCanonicalNormalizedDualizingComplex CA →
        ((ModuleCat.derivedExtensionOfScalars f).obj ω).IsCanonicalNormalizedDualizingComplex CB)
