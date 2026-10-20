/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.OpenSubset
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derivation.Affine

/-!
# Relative differentials on affine opens

For a morphism of schemes, sections of the relative differential sheaf on a compatible affine
open are canonically characterized by the Kähler differentials of the induced map on section
rings.
-/

@[expose] public section

open CategoryTheory Opposite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

variable {X S : Scheme.{u}}

/-- On compatible affine opens, sections of the relative differential sheaf are uniquely
linearly equivalent to the Kähler differentials of the induced map on section rings, compatibly
with the universal derivations. -/
theorem existsUnique_affineSectionsLinearEquiv
    (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    ∃! eΩ :
      Γ(Ω[f.toShHom], U) ≃ₗ[Γ(X, U)]
        CommRingCat.KaehlerDifferential (f.appLE V U hUV),
      ∀ a : Γ(X, U),
        eΩ (((d[f.toShHom]).app (op U)).d a) =
          CommRingCat.KaehlerDifferential.d a := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
