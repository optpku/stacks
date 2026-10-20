/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Perfect

@[expose] public section

universe u

#check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.isomorphicTensorDualOfPerfect :
    ∀ {R A : Type u} [CommRing R] [CommRing A]
      [IsNoetherianRing R] [IsNoetherianRing A]
      (f : R →+* A) (p : CategoryTheory.ModuleCat.UpperShriek.Presentation f)
      [f.IsPerfectRingMap],
      CategoryTheory.IsIsomorphic p.functor
        (CategoryTheory.derivedTensorChangeOfRings f
          (p.functor.obj (CategoryTheory.ModuleCat.single0 (ModuleCat.of R R)))))

/- Lemma 47.24.10: for a perfect homomorphism `f : R →+* A` of Noetherian rings,
the presentation-defined value `f⁗(K)` is isomorphic to the derived tensor product of `K`
over `R` with `f⁗(R)`. -/
@[stacks 0BZU] #check
  (CategoryTheory.ModuleCat.UpperShriek.Presentation.objIsomorphicTensorDualOfPerfect :
    ∀ {R A : Type u} [CommRing R] [CommRing A]
      [IsNoetherianRing R] [IsNoetherianRing A]
      (f : R →+* A) (p : CategoryTheory.ModuleCat.UpperShriek.Presentation f)
      [f.IsPerfectRingMap]
      (K : DerivedCategory (ModuleCat.{u, u} R)),
      CategoryTheory.IsIsomorphic (p.functor.obj K)
        ((CategoryTheory.derivedTensorChangeOfRings f
          (p.functor.obj (CategoryTheory.ModuleCat.single0 (ModuleCat.of R R)))).obj K))
