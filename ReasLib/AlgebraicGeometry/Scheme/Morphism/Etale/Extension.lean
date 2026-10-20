/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
import ReasLib.RingTheory.Etale.QuotientLift

/-!
# Extending étale morphisms

This file concerns extension of affine étale morphisms from closed subschemes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Etale

/-- An affine étale morphism over an affine closed subscheme extends to an affine étale
morphism over the ambient affine scheme, and its pullback is isomorphic to the original
morphism over the closed subscheme. -/
theorem exists_affine_extension_of_closedImmersion
    {X Z Z' : Scheme.{u}} (i : Z ⟶ X)
    [IsAffine X] [IsAffine Z] [IsClosedImmersion i]
    (g : Z' ⟶ Z) [IsAffine Z'] [Etale g] :
    ∃ (X' : Scheme.{u}) (_ : IsAffine X') (f : X' ⟶ X) (_ : Etale f),
      Nonempty (Over.mk g ≅ Over.mk (pullback.fst i f)) := sorry

/-- For a closed immersion and two schemes étale over the ambient scheme, every
morphism after pullback is induced by a span whose first leg pulls back to an
isomorphism. -/
theorem exists_extension_of_closedImmersion
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U U' : X.Etale)
    (h : (Scheme.smallEtalePullback i).obj U ⟶
      (Scheme.smallEtalePullback i).obj U') :
    ∃ (W : X.Etale) (a : W ⟶ U) (b : W ⟶ U')
      (e : (Scheme.smallEtalePullback i).obj W ≅
        (Scheme.smallEtalePullback i).obj U),
      e.hom = (Scheme.smallEtalePullback i).map a ∧
        h = e.inv ≫ (Scheme.smallEtalePullback i).map b := sorry

end AlgebraicGeometry.Etale
