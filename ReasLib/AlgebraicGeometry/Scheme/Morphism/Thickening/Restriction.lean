/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

/-!
# Restrictions of thickenings to open subschemes

A thickening transports opens of its closed part to opens of its ambient scheme. Compatible
opens over a base scheme determine a restricted bundled thickening, and the resulting square
with the two open immersions is cartesian.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Restricting a first-order thickening over an open of its target is again a first-order
thickening. -/
instance morphismRestrict_isFirstOrderThickening {X X' : Scheme.{u}} (i : X ⟶ X')
    [IsFirstOrderThickening i] (U' : X'.Opens) :
    IsFirstOrderThickening (i ∣_ U') := sorry

/-- Restriction of a morphism over `S` to an open of its target is again a morphism over `S`. -/
instance morphismRestrict_isOver {X X' : Scheme.{u}} (S : Scheme.{u}) (i : X ⟶ X')
    [X.Over S] [X'.Over S] [i.IsOver S] (U' : X'.Opens) :
    (i ∣_ U').IsOver S := sorry

namespace Thickening.Over

/-- The defining morphism of a bundled thickening over a scheme is a thickening. -/
instance instIsThickeningHom {X : Scheme.{u}} (T : Thickening.Over X) :
    IsThickening T.hom.left :=
  T.prop

end Thickening.Over

namespace IsThickening

/-- The order equivalence on open subschemes induced by the homeomorphism underlying a
thickening. -/
noncomputable def opensEquiv {Z Z' : Scheme.{u}} (i : Z ⟶ Z') [IsThickening i] :
    Z.Opens ≃o Z'.Opens :=
  (i.isClosedEmbedding.toHomeomorphOfSurjective i.surjective).opensCongr

/-- Pulling back the open transported along a thickening recovers the original open. -/
theorem preimage_opensEquiv {Z Z' : Scheme.{u}} (i : Z ⟶ Z') [IsThickening i]
    (V : Z.Opens) :
    i ⁻¹ᵁ (opensEquiv i V) = V := sorry

end IsThickening

namespace Thickening.Over

/-- The ambient open corresponding to a compatible open in the closed part remains over the
chosen open in the base. -/
theorem ambientOpen_le {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    IsThickening.opensEquiv T.hom.left V ≤ T.right.hom ⁻¹ᵁ U := sorry

/-- Restricting the defining morphism of a thickening to corresponding opens is again a
thickening. -/
instance restrictHom_isThickening {X : Scheme.{u}} (T : Thickening.Over X)
    (V : T.left.left.Opens) :
    IsThickening
      (T.hom.left.resLE (IsThickening.opensEquiv T.hom.left V) V
        (le_of_eq (IsThickening.preimage_opensEquiv T.hom.left V).symm)) := sorry

/-- The restrictions of the closed and ambient structural maps commute with the restricted
defining morphism. -/
theorem restrictHom_over {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    T.hom.left.resLE (IsThickening.opensEquiv T.hom.left V) V
        (le_of_eq (IsThickening.preimage_opensEquiv T.hom.left V).symm) ≫
      T.right.hom.resLE U (IsThickening.opensEquiv T.hom.left V)
        (ambientOpen_le T U V hV) =
    T.left.hom.resLE U V hV := sorry

/-- Restrict a bundled thickening over `X` to compatible opens in its closed part and in
`X`. -/
noncomputable def restrict {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    Thickening.Over U :=
  MorphismProperty.Arrow.mk
    (Over.homMk
      (T.hom.left.resLE (IsThickening.opensEquiv T.hom.left V) V
        (le_of_eq (IsThickening.preimage_opensEquiv T.hom.left V).symm))
      (restrictHom_over T U V hV) :
      Over.mk (T.left.hom.resLE U V hV) ⟶
        Over.mk (T.right.hom.resLE U (IsThickening.opensEquiv T.hom.left V)
          (ambientOpen_le T U V hV)))
    (restrictHom_isThickening T V)

/-- The closed part of a restricted thickening is the prescribed open over the restricted
base. -/
theorem restrict_left {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    (restrict T U V hV).left = Over.mk (T.left.hom.resLE U V hV) := sorry

/-- The ambient part of a restricted thickening is the corresponding transported open over
the restricted base. -/
theorem restrict_right {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    (restrict T U V hV).right =
      Over.mk (T.right.hom.resLE U (IsThickening.opensEquiv T.hom.left V)
        (ambientOpen_le T U V hV)) := sorry

/-- The defining morphism of a restricted thickening is the restriction of the original
defining morphism to the corresponding opens. -/
theorem restrict_hom {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    (restrict T U V hV).hom.left =
      T.hom.left.resLE (IsThickening.opensEquiv T.hom.left V) V
        (le_of_eq (IsThickening.preimage_opensEquiv T.hom.left V).symm) := sorry

/-- The defining morphism of a restricted thickening forms a pullback square with the two
open immersions. -/
theorem restrictSquare {X : Scheme.{u}} (T : Thickening.Over X)
    (U : X.Opens) (V : T.left.left.Opens) (hV : V ≤ T.left.hom ⁻¹ᵁ U) :
    IsPullback V.ι (restrict T U V hV).hom.left T.hom.left
      (IsThickening.opensEquiv T.hom.left V).ι := sorry

end Thickening.Over

end AlgebraicGeometry
