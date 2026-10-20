/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Length.GeometricPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Noetherian

/-!
# Length of a module at an ordinary point

Numerical length at a point is the supremum of the geometric-stalk lengths above it.
For coherent modules it agrees with geometric-stalk length and the chartwise length predicate.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The length of an `𝒪_X`-module at a point of `|X|` is the supremum of étale-stalk
lengths at geometric points over that point. -/
noncomputable def lengthAt (F : X.Modules) (x : Points X) : ℕ∞ :=
  ⨆ p : {p : GeometricPoint X // p.liesOver x}, lengthAtGeometricPoint F p.1

/-- The length at a point is the supremum of geometric-stalk lengths above it. -/
theorem lengthAt_eq (F : X.Modules) (x : Points X) :
    lengthAt F x =
      ⨆ p : {p : GeometricPoint X // p.liesOver x}, lengthAtGeometricPoint F p.1 :=
  rfl

/-- For a coherent module on a locally Noetherian algebraic space, the length at a point
agrees with the étale-stalk length at any geometric point over it. -/
theorem lengthAt_eq_lengthAtGeometricPoint [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (x : Points X)
    (xbar : GeometricPoint X) (hx : xbar.liesOver x) :
    lengthAt F x = lengthAtGeometricPoint F xbar :=
  sorry

/-- The numerical length at a point satisfies the chartwise length predicate. -/
theorem hasLengthAt_lengthAt [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (x : Points X) :
    hasLengthAt F x (lengthAt F x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
