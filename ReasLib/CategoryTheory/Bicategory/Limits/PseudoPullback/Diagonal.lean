/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone

/-!
# Diagonal cones for bicategorical pseudo-pullbacks

The diagonal cone on a `1`-morphism is the canonical cone with two identity legs. It is the
source object for relative-diagonal constructions in any bicategory admitting the relevant
pseudo-pullback.
-/

@[expose] public section

open CategoryTheory
open Bicategory

universe uB vB wB

namespace CategoryTheory.Bicategory.PseudoPullbackCone

variable {B : Type uB} [Bicategory.{wB, vB} B]

/-- The diagonal cone on a `1`-morphism `F : x ⟶ y` in an arbitrary bicategory. Both legs are
the identity of `x`; its universal lift is the relative diagonal of `F`. -/
def diagonal {x y : B} (F : x ⟶ y) : PseudoPullbackCone F F where
  pt := x
  fst := 𝟙 x
  snd := 𝟙 x
  iso := Iso.refl _

/-- The apex of the diagonal pseudo-pullback cone is its source object. -/
@[simp]
theorem diagonal.pt {x y : B} (F : x ⟶ y) :
    (diagonal F).pt = x := sorry

/-- The first leg of the diagonal pseudo-pullback cone is the identity. -/
@[simp]
theorem diagonal.fst {x y : B} (F : x ⟶ y) :
    (diagonal F).fst = (𝟙 x : x ⟶ x) := sorry

/-- The second leg of the diagonal pseudo-pullback cone is the identity. -/
@[simp]
theorem diagonal.snd {x y : B} (F : x ⟶ y) :
    (diagonal F).snd = (𝟙 x : x ⟶ x) := sorry

/-- The comparison `2`-isomorphism of the diagonal pseudo-pullback cone is the identity. -/
@[simp]
theorem diagonal.iso {x y : B} (F : x ⟶ y) :
    (diagonal F).iso = Iso.refl ((𝟙 x : x ⟶ x) ≫ F) := sorry

/-- The forward comparison `2`-cell of the diagonal cone is the identity. -/
@[simp]
theorem diagonal.iso.hom {x y : B} (F : x ⟶ y) :
    (diagonal F).iso.hom = 𝟙 ((𝟙 x : x ⟶ x) ≫ F) := sorry

/-- The inverse comparison `2`-cell of the diagonal cone is the identity. -/
@[simp]
theorem diagonal.iso.inv {x y : B} (F : x ⟶ y) :
    (diagonal F).iso.inv = 𝟙 ((𝟙 x : x ⟶ x) ≫ F) := sorry

/- Data audit (mathlib 4.32): `diagonal` reports only `propext`, `Classical.choice`, and
`Quot.sound`. Its apex, identity legs, and identity comparison are explicit and do not depend
on `sorryAx`. -/

end CategoryTheory.Bicategory.PseudoPullbackCone
