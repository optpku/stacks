/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.Perfect
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 47.13.9: for a commutative ring homomorphism with perfect target module,
derived coextension is naturally isomorphic to derived tensor change of rings with
the coextension of the source regular module; the source algebra case uses
`f = algebraMap R A`. -/
@[stacks 0BZE] #check
  (CategoryTheory.ModuleCat.DerivedCoextension.isomorphicTensorDualOfPerfect :
    ∀ {R A : Type u} [CommRing R] [CommRing A]
      (f : R →+* A) (hA : ModuleCat.IsPerfect f.targetModule),
      CategoryTheory.IsIsomorphic (CategoryTheory.ModuleCat.derivedCoextensionOfScalars f)
        (CategoryTheory.derivedTensorChangeOfRings f
          ((CategoryTheory.ModuleCat.derivedCoextensionOfScalars f).obj
            (CategoryTheory.ModuleCat.single0 (ModuleCat.of R R)))))

#check
  (CategoryTheory.ModuleCat.DerivedCoextension.objIsomorphicTensorDualOfPerfect :
    ∀ {R A : Type u} [CommRing R] [CommRing A]
      (f : R →+* A) (hA : ModuleCat.IsPerfect f.targetModule)
      (K : DerivedCategory (ModuleCat R)),
      CategoryTheory.IsIsomorphic ((CategoryTheory.ModuleCat.derivedCoextensionOfScalars f).obj K)
        ((CategoryTheory.derivedTensorChangeOfRings f
          ((CategoryTheory.ModuleCat.derivedCoextensionOfScalars f).obj
            (CategoryTheory.ModuleCat.single0 (ModuleCat.of R R)))).obj K))
