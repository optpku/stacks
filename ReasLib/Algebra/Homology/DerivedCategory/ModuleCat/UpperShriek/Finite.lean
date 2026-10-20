/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.InvertibleKernel
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Composition

@[expose] public section

open CategoryTheory
noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek.Presentation

variable {R A : Type u} [CommRing R] [CommRing A]

/-- For a finite homomorphism of Noetherian rings, the upper-shriek functor associated
to a presentation is naturally isomorphic to derived coextension of scalars. -/
theorem isomorphicDerivedCoextensionOfFinite
    [IsNoetherianRing R] [IsNoetherianRing A]
    (φ : R →+* A) (hφ : φ.Finite)
    (p : CategoryTheory.ModuleCat.UpperShriek.Presentation φ) :
    IsIsomorphic p.functor (ModuleCat.derivedCoextensionOfScalars φ) := sorry

/-- Evaluating the upper-shriek comparison for a finite homomorphism at a derived
module gives isomorphic objects. -/
theorem objIsomorphicDerivedCoextensionOfFinite
    [IsNoetherianRing R] [IsNoetherianRing A]
    (φ : R →+* A) (hφ : φ.Finite)
    (p : CategoryTheory.ModuleCat.UpperShriek.Presentation φ)
    (K : DerivedCategory (ModuleCat R)) :
    IsIsomorphic (p.functor.obj K) ((ModuleCat.derivedCoextensionOfScalars φ).obj K) := sorry

end CategoryTheory.ModuleCat.UpperShriek.Presentation
