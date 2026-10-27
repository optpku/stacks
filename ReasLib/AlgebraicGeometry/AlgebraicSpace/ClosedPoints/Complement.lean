/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Complement

/-! # Complements of closed points of algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The open complement `X \ {x}` of a closed point of a decent algebraic space. -/
def closedPointComplement {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    {x : Points X} (hx : x ∈ closedPoints (Points X)) : AlgebraicSpace S :=
  @closedImmersionComplement _ _ _ (X.fromSpecResidueField x)
    (isClosedImmersion_fromSpecResidueField hx)

/-- The open immersion `X \ {x} ⟶ X` of a closed point of a decent algebraic space. -/
def closedPointComplementι {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    {x : Points X} (hx : x ∈ closedPoints (Points X)) :
    closedPointComplement X hx ⟶ X :=
  @closedImmersionComplementι _ _ _ (X.fromSpecResidueField x)
    (isClosedImmersion_fromSpecResidueField hx)

/-- The complement of a closed point is an open immersion into `X`. -/
instance instIsOpenImmersion_closedPointComplementι {S : Scheme.{u}}
    (X : AlgebraicSpace S) [IsDecent X] {x : Points X}
    (hx : x ∈ closedPoints (Points X)) :
    IsOpenImmersion (closedPointComplementι X hx) :=
  @instIsOpenImmersion_closedImmersionComplementι _ _ _
    (X.fromSpecResidueField x) (isClosedImmersion_fromSpecResidueField hx)

end AlgebraicGeometry.AlgebraicSpace
