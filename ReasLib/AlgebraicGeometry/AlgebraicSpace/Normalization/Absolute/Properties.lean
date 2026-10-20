/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normalization.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Properties of the absolute normalization of algebraic spaces

The absolute normalization morphism is surjective, bijects codimension-zero points,
and uniquely lifts morphisms from normal algebraic spaces preserving such points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The canonical absolute normalization morphism of an algebraic space with finitely
many irreducible components on compact opens is surjective. -/
@[stacks 0BB4]
instance instSurjective_normalizationTo {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Surjective X.normalizationTo :=
  sorry

namespace Normalization

/-- The canonical absolute normalization morphism of an algebraic space with finitely
many irreducible components on compact opens induces a bijection on codimension-zero
points. -/
@[stacks 0BB4]
theorem bijOn_codimZeroPoints {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasFiniteIrreducibleComponentsOnCompactOpens X] :
    Set.BijOn (Points.map X.normalizationTo)
      (codimZeroPoints X.normalization) (codimZeroPoints X) :=
  sorry

/-- A morphism from a normal algebraic space preserving codimension-zero points factors
uniquely through the absolute normalization of an algebraic space with finitely many
irreducible components on compact opens. -/
@[stacks 0BB4]
theorem existsUnique_lift_of_isNormal {S : Scheme.{u}} {X : AlgebraicSpace S}
    [HasFiniteIrreducibleComponentsOnCompactOpens X] {Z : AlgebraicSpace S}
    [IsNormal Z] (f : Z ⟶ X) (hf : mapsCodimZero f) :
    ∃! h : Z ⟶ X.normalization, h ≫ X.normalizationTo = f :=
  sorry

end Normalization

end AlgebraicGeometry.AlgebraicSpace
