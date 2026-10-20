/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ValuativeCriterion.DVR.Factorization

/-!
# Refined Noetherian DVR valuative criterion for separatedness

A locally finite-type quasi-separated morphism of algebraic spaces into a
locally Noetherian target is separated as soon as every DVR valuative square
whose generic arrow factors through a dense finite-type morphism has at most
one dotted lift.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace ValuativeCriterion.DVR.Along

/-- Let `S` be a scheme. Let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of
algebraic spaces over `S`. Assume that `Y` is locally Noetherian, that `f` is
locally of finite type and quasi-separated, that `h` is of finite type, and
that the image of `|h| : |U| ⟶ |X|` is dense in `|X|`. If every commutative
solid diagram `Spec(K) ⟶ U ⟶ X` over `Spec(A) ⟶ Y`, where `A` is a discrete
valuation ring with field of fractions `K`, has at most one dotted lift to
`X`, then `f` is separated. -/
theorem separated_of_uniqueness {S : Scheme.{u}} {U X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (h : U ⟶ X) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    [QuasiSeparated f] [FiniteType h] [Dominant h]
    (h_uniqueness : Uniqueness h f) : Separated f :=
  sorry

end ValuativeCriterion.DVR.Along

end AlgebraicGeometry.AlgebraicSpace
