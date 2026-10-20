/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.PrincipalOpen.Cech.Derived
import StacksCheckRecall

universe u

/- Lemma 36.9.4: for the union of a finite family of principal opens of `Spec(A)`,
the canonical functorial comparison from the total strictly indexed alternating Cech complex
of a termwise quasi-coherent complex to derived sections on the union is an isomorphism in
`D(A)`. -/
@[stacks 08D2] #check
  (AlgebraicGeometry.Scheme.PrincipalOpenCech.comparison_isIso :
    ∀ {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
      (K : AlgebraicGeometry.Scheme.PrincipalOpenCech.QuasiCoherentComplex A),
      CategoryTheory.IsIso
        ((AlgebraicGeometry.Scheme.PrincipalOpenCech.comparisonHom f).app K))
