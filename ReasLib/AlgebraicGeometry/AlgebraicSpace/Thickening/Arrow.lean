/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening

/-!
# Morphisms of thickenings of algebraic spaces

Bundled thickenings of algebraic spaces over a scheme `S` are arrows whose
structural morphism is a thickening. Morphisms of thickenings are commutative
squares, and thickenings over an algebraic space `B` are the same arrows in
the over category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The category of thickenings of algebraic spaces over `S`. -/
abbrev Thickening (S : Scheme.{u}) :=
  MorphismProperty.Arrow
    (@IsThickening S : MorphismProperty (AlgebraicSpace S)) ⊤ ⊤

namespace Thickening

/-- Construct a bundled thickening from a morphism of algebraic spaces carrying
the thickening property. -/
def of {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsThickening i] : Thickening S :=
  MorphismProperty.Arrow.mk i (inferInstance : IsThickening i)

/-- The defining morphism of a bundled thickening constructed by `Thickening.of`. -/
theorem of_hom {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsThickening i] : (of i).hom = i :=
  sorry

/-- Construct a morphism of thickenings from maps on the closed subspaces and
ambient spaces, together with their commutative-square equation. -/
def homMk {S : Scheme.{u}} {T U : Thickening S} (f : T.left ⟶ U.left)
    (f' : T.right ⟶ U.right) (w : f ≫ U.hom = T.hom ≫ f') : T ⟶ U :=
  MorphismProperty.Arrow.homMk f f' w

/-- The map on closed subspaces of a morphism constructed by `Thickening.homMk`. -/
theorem homMk_left {S : Scheme.{u}} {T U : Thickening S} (f : T.left ⟶ U.left)
    (f' : T.right ⟶ U.right) (w : f ≫ U.hom = T.hom ≫ f') :
    (homMk f f' w).left = f :=
  sorry

/-- The map on ambient spaces of a morphism constructed by `Thickening.homMk`. -/
theorem homMk_right {S : Scheme.{u}} {T U : Thickening S} (f : T.left ⟶ U.left)
    (f' : T.right ⟶ U.right) (w : f ≫ U.hom = T.hom ≫ f') :
    (homMk f f' w).right = f' :=
  sorry

namespace Hom

/-- The commutative-square equation satisfied by a morphism of thickenings. -/
theorem w {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    g.left ≫ U.hom = T.hom ≫ g.right :=
  sorry

end Hom

/-- The category of thickenings of algebraic spaces over a fixed algebraic space
`B`. -/
abbrev Over {S : Scheme.{u}} (B : AlgebraicSpace S) :=
  MorphismProperty.Arrow
    (MorphismProperty.inverseImage
      (@IsThickening S : MorphismProperty (AlgebraicSpace S))
      (CategoryTheory.Over.forget B)) ⊤ ⊤

namespace Over

/-- The underlying morphism of algebraic spaces of a thickening over `B` is a
thickening. -/
theorem isThickening {S : Scheme.{u}} {B : AlgebraicSpace S}
    (T : Thickening.Over B) :
    IsThickening ((CategoryTheory.Over.forget B).map T.hom) :=
  sorry

end Over

end Thickening

end AlgebraicGeometry.AlgebraicSpace
