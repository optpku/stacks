/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Comma

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A scheme morphism is a thickening if it is a closed immersion and is surjective on
underlying points. -/
class IsThickening {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop
    extends IsClosedImmersion f, Surjective f

/-- A closed immersion that is surjective on underlying points is a thickening. -/
instance instIsThickening {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsClosedImmersion f] [Surjective f] : IsThickening f := sorry

/-- Being a thickening is equivalent to being both a closed immersion and surjective on
underlying points. -/
theorem isThickening_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsThickening f ↔ IsClosedImmersion f ∧ Surjective f := sorry

/-- The composite of two thickenings is a thickening. -/
@[stacks 0BPE]
instance IsThickening.comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [IsThickening f] [IsThickening g] : IsThickening (f ≫ g) := sorry

/-- A finite-order thickening is a closed immersion whose kernel ideal sheaf is nilpotent. -/
class IsFiniteOrderThickening {X X' : Scheme.{u}} (i : X ⟶ X') : Prop where
  /-- The defining morphism is a closed immersion. -/
  isClosedImmersion : IsClosedImmersion i
  /-- The ideal sheaf defining the closed subscheme is nilpotent. -/
  ker_isNilpotent : IsNilpotent i.ker

/-- A finite-order thickening has the underlying thickening property. -/
instance instIsThickeningOfIsFiniteOrderThickening {X X' : Scheme.{u}} (i : X ⟶ X')
    [IsFiniteOrderThickening i] : IsThickening i := sorry

/-- The closed-immersion and nilpotence conditions defining a finite-order thickening. -/
theorem isFiniteOrderThickening_iff {X X' : Scheme.{u}} (i : X ⟶ X') :
    IsFiniteOrderThickening i ↔ IsClosedImmersion i ∧ IsNilpotent i.ker := sorry

/-- An `n`th-order thickening is a closed immersion whose kernel ideal sheaf has
`(n + 1)`st power zero. -/
class IsNthOrderThickening (n : ℕ) {X X' : Scheme.{u}} (i : X ⟶ X') : Prop
    extends IsFiniteOrderThickening i where
  /-- The `(n + 1)`st power of the defining ideal sheaf vanishes. -/
  ker_pow_succ : i.ker ^ (n + 1) = 0

/-- The identity of a scheme is an `n`th-order thickening for every `n`. -/
instance instIsNthOrderThickeningIdentity (n : ℕ) (X : Scheme.{u}) :
    IsNthOrderThickening n (𝟙 X) := sorry

/-- The closed-immersion and ideal-power conditions defining an `n`th-order thickening. -/
theorem isNthOrderThickening_iff (n : ℕ) {X X' : Scheme.{u}} (i : X ⟶ X') :
    IsNthOrderThickening n i ↔ IsClosedImmersion i ∧ i.ker ^ (n + 1) = 0 := sorry

/-- A first-order thickening is a `1`st-order thickening. -/
abbrev IsFirstOrderThickening {X X' : Scheme.{u}} (i : X ⟶ X') : Prop :=
  IsNthOrderThickening 1 i

/-- The square-zero ideal-sheaf characterization of a first-order thickening. -/
theorem isFirstOrderThickening_iff {X X' : Scheme.{u}} (i : X ⟶ X') :
    IsFirstOrderThickening i ↔ IsClosedImmersion i ∧ i.ker ^ 2 = 0 := sorry

/-- The category of thickenings, with commutative squares as morphisms. -/
abbrev Thickening :=
  MorphismProperty.Arrow (@IsThickening : MorphismProperty Scheme.{u}) ⊤ ⊤

namespace Thickening

/-- Construct a bundled thickening from a scheme morphism carrying the thickening property. -/
def of {X X' : Scheme.{u}} (i : X ⟶ X') [IsThickening i] : Thickening.{u} :=
  MorphismProperty.Arrow.mk i (inferInstance : IsThickening i)

/-- The defining morphism of a bundled thickening constructed by `Thickening.of`. -/
theorem of_hom {X X' : Scheme.{u}} (i : X ⟶ X') [IsThickening i] :
    (of i).hom = i := sorry

/-- Construct a morphism of thickenings from its maps on the closed subschemes and ambient
schemes, together with their commutative-square equation. -/
def homMk {T U : Thickening.{u}} (f : T.left ⟶ U.left) (f' : T.right ⟶ U.right)
    (w : f ≫ U.hom = T.hom ≫ f') : T ⟶ U :=
  MorphismProperty.Arrow.homMk f f' w

/-- The map on closed subschemes of a morphism constructed by `Thickening.homMk`. -/
theorem homMk_left {T U : Thickening.{u}} (f : T.left ⟶ U.left)
    (f' : T.right ⟶ U.right) (w : f ≫ U.hom = T.hom ≫ f') :
    (homMk f f' w).left = f := sorry

/-- The map on ambient schemes of a morphism constructed by `Thickening.homMk`. -/
theorem homMk_right {T U : Thickening.{u}} (f : T.left ⟶ U.left)
    (f' : T.right ⟶ U.right) (w : f ≫ U.hom = T.hom ≫ f') :
    (homMk f f' w).right = f' := sorry

namespace Hom

/-- The commutative-square equation satisfied by a morphism of thickenings. -/
theorem w {T U : Thickening.{u}} (g : T ⟶ U) :
    g.left ≫ U.hom = T.hom ≫ g.right := sorry

end Hom

/-- The category of thickenings between schemes over a fixed base scheme `S`. -/
abbrev Over (S : Scheme.{u}) :=
  MorphismProperty.Arrow
    (MorphismProperty.inverseImage (@IsThickening : MorphismProperty Scheme.{u})
      (CategoryTheory.Over.forget S)) ⊤ ⊤

namespace Over

/-- The underlying scheme morphism of a thickening over `S` is a thickening. -/
theorem isThickening (S : Scheme.{u}) (T : Thickening.Over S) :
    IsThickening ((CategoryTheory.Over.forget S).map T.hom) := sorry

end Over

end Thickening

end AlgebraicGeometry
