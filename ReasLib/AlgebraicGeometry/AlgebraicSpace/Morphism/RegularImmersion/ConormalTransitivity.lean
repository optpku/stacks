/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.Implications
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Transitivity.Splitting

/-!
# Conormal transitivity for regular immersions of algebraic spaces

The canonical conormal transitivity sequence for an `H₁`-regular immersion
followed by an immersion is short exact and splits étale locally.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Hom.Conormal.Transitivity

namespace IsH1RegularImmersion

/-- The canonical conormal transitivity sequence is short exact and splits étale locally. -/
theorem conormalTransitivity_isShortExactLocallySplit
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsH1RegularImmersion i] [IsImmersion j] :
    IsShortExactLocallySplit i j :=
  sorry

/-- The canonical conormal transitivity sequence associated to an `H₁`-regular immersion is short exact. -/
theorem conormalTransitivity_shortExact
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsH1RegularImmersion i] [IsImmersion j] :
    (complex i j).ShortExact :=
  (conormalTransitivity_isShortExactLocallySplit i j).1

/-- The first canonical conormal transitivity map is a monomorphism. -/
instance mono_conormalTransitivity_baseChange
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsH1RegularImmersion i] [IsImmersion j] :
    Mono (baseChange i j) :=
  (conormalTransitivity_shortExact i j).mono_f

end IsH1RegularImmersion

end AlgebraicGeometry.AlgebraicSpace
