module

public import ReasLib.CategoryTheory.Bicategory.HomProperty
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Symmetry.Bilimit

/-!
# Hom properties stable under bicategorical base change

This file is the bicategorical analogue of mathlib's
`MorphismProperty.IsStableUnderBaseChange` API. A `Bicategory.HomProperty` is stable under
base change when membership of the right leg of any bilimit pseudopullback square implies
membership of its first projection.

The fixed-leg class `IsStableUnderBaseChangeAlong f` supports local hypotheses, while a global
stability instance supplies it automatically. The second-projection theorem is derived
symmetrically, so the two projection APIs share one orientation convention.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.HomProperty

variable {B : Type u} [Bicategory.{w, v} B]
variable (Q : HomProperty (fun X : B ↦ X))

/-- A bicategorical hom property is stable under base change when the first projection of
every bilimit pseudopullback cone satisfies the property whenever its right cospan leg does.

Quantifying over every bilimit cone makes the condition independent of any chosen
pseudopullback construction. -/
class IsStableUnderBaseChange : Prop where
  /-- Transport membership from the right cospan leg to the first projection of any bilimit
  pseudopullback cone. -/
  of_isBilimit {X Y S : B} {f : X ⟶ S} {g : Y ⟶ S}
    (P : PseudoPullbackCone f g) (hP : P.IsBilimit)
    (hg : Q Y S g) : Q P.pt X P.fst

/-- Stability of a bicategorical hom property under base change along one fixed
`1`-morphism. The fixed morphism is the left cospan leg; the property is transported from
the varying right leg to the first projection. -/
class IsStableUnderBaseChangeAlong {X S : B} (f : X ⟶ S) : Prop where
  /-- Transport membership from the varying right cospan leg to the first projection of any
  bilimit pseudopullback cone over `f`. -/
  of_isBilimit {Y : B} {g : Y ⟶ S}
    (P : PseudoPullbackCone f g) (hP : P.IsBilimit)
    (hg : Q Y S g) : Q P.pt X P.fst

/-- Global base-change stability supplies stability along every fixed `1`-morphism. -/
instance isStableUnderBaseChangeAlong
    [Q.IsStableUnderBaseChange] {X S : B} (f : X ⟶ S) :
    Q.IsStableUnderBaseChangeAlong f := sorry

/-- The first projection of a bilimit pseudopullback inherits the hom property from the
right cospan leg. -/
theorem pseudoPullback_fst
    {X Y S : B} {f : X ⟶ S} {g : Y ⟶ S}
    [Q.IsStableUnderBaseChangeAlong f]
    (P : PseudoPullbackCone f g) (hP : P.IsBilimit)
    (hg : Q Y S g) :
    Q P.pt X P.fst := sorry

/-- The second projection of a bilimit pseudopullback inherits the hom property from the
left cospan leg. This is the first-projection theorem applied after reversing the two legs. -/
theorem pseudoPullback_snd
    {X Y S : B} {f : X ⟶ S} {g : Y ⟶ S}
    [Q.IsStableUnderBaseChangeAlong g]
    (P : PseudoPullbackCone f g) (hP : P.IsBilimit)
    (hf : Q X S f) :
    Q P.pt Y P.snd := sorry

end Bicategory.HomProperty

end CategoryTheory
