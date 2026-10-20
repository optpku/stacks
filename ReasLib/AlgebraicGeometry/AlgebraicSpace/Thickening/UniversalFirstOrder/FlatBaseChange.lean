/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.UniversalFirstOrder.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange

/-!
# Flat base change of universal first-order thickenings of algebraic spaces

If a fibre product square of algebraic spaces has formally unramified horizontal
arrows and a flat ambient morphism, the canonical comparison of universal
first-order thickenings is flat and the associated conormal comparison is an
isomorphism.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry (Scheme)
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder

/-- If the original square is cartesian and the ambient morphism is flat, the
canonical map of universal first-order thickenings is flat. -/
instance comparison_flat {S : Scheme.{u}} {X Y Z W Z' W' : AlgebraicSpace S}
    (g : X ⟶ Y) (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)] [Flat g]
    (leftSq : IsPullback f (iZ ≫ fZ) (iW ≫ fW) g) :
    Flat (comparison iZ fZ iW fW f g ⟨leftSq.w⟩) :=
  sorry

/-- If the original square is cartesian and the ambient morphism is flat, the
canonical comparison of conormal sheaves of the universal first-order
thickenings is an isomorphism. -/
instance conormalMap_isIso {S : Scheme.{u}} {X Y Z W Z' W' : AlgebraicSpace S}
    (g : X ⟶ Y) (iZ : Z ⟶ Z') (fZ : Z' ⟶ X) (iW : W ⟶ W') (fW : W' ⟶ Y)
    (f : Z ⟶ W) [IsUniversalFirstOrder iZ fZ] [IsUniversalFirstOrder iW fW]
    [FormallyUnramified (iZ ≫ fZ)] [FormallyUnramified (iW ≫ fW)] [Flat g]
    (leftSq : IsPullback f (iZ ≫ fZ) (iW ≫ fW) g) :
    IsIso (conormalMap iZ fZ iW fW f g ⟨leftSq.w⟩) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder
