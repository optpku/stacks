/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Dualizing

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek

variable {R A : Type u} [CommRing R] [CommRing A]

/- Lemma 47.24.3 -/
@[stacks 0BZL] #check (CategoryTheory.ModuleCat.UpperShriek.Presentation.mapsDualizingComplex :
  ∀ {R A : Type u} [CommRing R] [CommRing A]
    [IsNoetherianRing R] [IsNoetherianRing A]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} R))]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
    (f : R →+* A) (hf : f.FiniteType) (p : CategoryTheory.ModuleCat.UpperShriek.Presentation f)
    (CR : DerivedCategory.CanonicalClosedPresentation (A := R))
    (CA : DerivedCategory.CanonicalClosedPresentation (A := A))
    (ω : DerivedCategory (ModuleCat.{u, u} R))
    (hω : ω.IsDualizingComplex CR.comparison.closed),
    (p.functor.obj ω).IsDualizingComplex CA.comparison.closed)

end CategoryTheory.ModuleCat.UpperShriek
