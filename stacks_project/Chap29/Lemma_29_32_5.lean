/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Differentials.Affine
import StacksCheckRecall

open CategoryTheory Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

/- Lemma 29.32.5: for a morphism of schemes and compatible affine opens in its source and
target, sections of the relative differential sheaf are uniquely linearly equivalent to the
Kähler differentials of the induced map on section rings, compatibly with the universal
derivations. -/
@[stacks 01UT] #check
  (AlgebraicGeometry.Scheme.RelativeDifferentials.existsUnique_affineSectionsLinearEquiv :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens),
      IsAffineOpen U → IsAffineOpen V → ∀ hUV : U ≤ f ⁻¹ᵁ V,
        ∃! eΩ :
          Γ(Ω[f.toShHom], U) ≃ₗ[Γ(X, U)]
            CommRingCat.KaehlerDifferential (f.appLE V U hUV),
          ∀ a : Γ(X, U),
            eΩ (((d[f.toShHom]).app (op U)).d a) =
              CommRingCat.KaehlerDifferential.d a)
