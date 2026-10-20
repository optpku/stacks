/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.LocalCohomology.Frobenius
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DerivedCategory.CechCompletion

universe u

namespace CategoryTheory.DerivedCategory.LocalCohomology

/- Lemma 51.19.2: if a prime `p` vanishes in `A` and `I` is finitely generated, then
derived extension of `RΓ_{V(I)}(A)` along Frobenius is isomorphic to `RΓ_{V(I)}(A)` itself. -/
@[stacks 0EC6] #check
  (CategoryTheory.DerivedCategory.LocalCohomology.frobeniusBaseChangeIso :
    ∀ {A : Type u} [CommRing A]
      (p : ℕ) [Fact p.Prime] (hp : (p : A) = 0) (I : Ideal A) (_ : I.FG),
      ∃ (RΓ : DerivedCategory (ModuleCat A) ⥤ IdealPowerTorsion I),
        ∃ (_ : IdealPowerTorsion.inclusion I ⊣ RΓ),
          Nonempty
            ((ModuleCat.derivedExtensionOfScalars (RingHom.frobeniusOfPrime p hp)).obj
                (RΓ.obj regular).obj ≅
              (RΓ.obj regular).obj))

end CategoryTheory.DerivedCategory.LocalCohomology
