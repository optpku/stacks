/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.Smooth
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.62.3: if `f : X ⟶ S` is a local complete intersection morphism,
`U` is an open subscheme of `X`, and `i : U.toScheme ⟶ P` is an immersion over `S`
into a scheme smooth over `S`, then `i` is a Koszul-regular immersion. -/
@[stacks 069G] #check
  (AlgebraicGeometry.IsKoszulRegularImmersion.of_localCompleteIntersection_over_smooth :
    ∀ {X P S : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ S) (p : P ⟶ S) (U : X.Opens) (i : U.toScheme ⟶ P)
      [AlgebraicGeometry.Smooth p] [AlgebraicGeometry.IsImmersion i]
      (h_lci : AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f)
      (h_over : i ≫ p = U.ι ≫ f),
      AlgebraicGeometry.IsKoszulRegularImmersion i)
