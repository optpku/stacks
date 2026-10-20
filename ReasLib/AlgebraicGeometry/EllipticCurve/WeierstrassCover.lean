/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.EllipticCurve.WeierstrassFamily
public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothOnSchemes
public import ReasLib.AlgebraicGeometry.EllipticCurve.AlgebraicStack

/-!
# The universal Weierstrass smooth cover

The classifying morphism of the universal Weierstrass family is smooth and surjective.
-/

@[expose] public section

open AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom (SmoothOnSchemes)

universe u

namespace AlgebraicGeometry.WeierstrassScheme

/-- The classifying morphism of the universal Weierstrass family is smooth on schemes. -/
instance classifying_smooth :
    SmoothOnSchemes classifying.{u} := sorry

/-- The classifying morphism of the universal Weierstrass family is surjective on schemes. -/
theorem classifying_surjective :
    EllipticCurve.Moduli.surjectiveOnSchemes classifying.{u} := sorry

/-- The classifying morphism of the universal Weierstrass family is smooth and surjective
on schemes. -/
theorem classifying_smooth_surjective :
    Groupoids.Hom.SmoothOnSchemes classifying.{u} ∧
      EllipticCurve.Moduli.surjectiveOnSchemes classifying.{u} :=
  ⟨classifying_smooth, classifying_surjective⟩

end AlgebraicGeometry.WeierstrassScheme
