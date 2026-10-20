/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.Normalized
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Nagata
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper

/-!
# Nagata properties of normalized blowups of algebraic spaces

If `X` is a Nagata decent algebraic space, a normalized blowup of `X` at a closed
point has normal Nagata source, and the composite morphism to `X` is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup

/-- The source of a normalized blowup of a Nagata algebraic space at a closed point is
normal. -/
theorem source_isNormal {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] [IsNagata X]
    (s : NormalizedBlowup X) :
    IsNormal s.source :=
  sorry

/-- The source of a normalized blowup of a Nagata algebraic space at a closed point is
Nagata. -/
theorem source_isNagata {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] [IsNagata X]
    (s : NormalizedBlowup X) :
    IsNagata s.source :=
  sorry

/-- The normalized blowup morphism of a Nagata algebraic space at a closed point is
proper. -/
theorem hom_isProper {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [HasFiniteIrreducibleComponentsOnCompactOpens X] [IsNagata X]
    (s : NormalizedBlowup X) :
    Proper s.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.NormalizedBlowup
