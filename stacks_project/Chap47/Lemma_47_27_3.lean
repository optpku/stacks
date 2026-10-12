/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.RelativeDualizing

open CategoryTheory
open CategoryTheory.ModuleCat

universe u

/- Lemma 47.27.3: for a flat finite-type algebra over Noetherian rings, the
presentation-defined upper-shriek object is a relative dualizing complex. -/
@[stacks 0E2E] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.relativeDualizing_isRelativeDualizingComplex_of_flat :
    ∀ {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R A] [Module.Flat R A],
      (p : CategoryTheory.ModuleCat.UpperShriek.Presentation (algebraMap R A)) →
        @CategoryTheory.DerivedCategory.IsRelativeDualizingComplex R _ A _ _ inferInstance
          (Algebra.FinitePresentation.of_finiteType.mp inferInstance)
          (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))))
