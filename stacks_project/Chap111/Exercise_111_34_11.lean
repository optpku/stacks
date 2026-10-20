/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Finite
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Exercise 111.34.11: a finite type algebra over a Noetherian ring whose spectrum
embeds as a closed subscheme of projective space is finite as a module over the base. -/
@[stacks 0EG6] #check
  (AlgebraicGeometry.ProjectiveSpace.moduleFinite_of_closedImmersion :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      [IsNoetherianRing A] [Algebra.FiniteType A B] {n : ℕ},
      (i : Spec (.of B) ⟶ AlgebraicGeometry.ProjectiveSpace.scheme A n) →
        [IsClosedImmersion i] →
        i ≫ AlgebraicGeometry.ProjectiveSpace.toSpec A n =
          Spec.map (CommRingCat.ofHom (algebraMap A B)) →
        Module.Finite A B)
