module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.ProjectionEquivalence.Left
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Symmetry.Bilimit

/-!
# Right-leg equivalences and pseudopullback projections

This directional leaf obtains the right-leg form of the projection-equivalence theorem by
applying the readable pseudopullback symmetry to the left-leg owner. The standard right cone is
literally the swapped standard left cone, and the selected equivalence on the first projection
is the existing second-projection equivalence of the swapped input.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- The standard pseudopullback cone of `f` and `g` when the right leg `g` is equipped with
equivalence data. It is the swap of the standard left-equivalence cone for `g` and `f`. -/
@[stacks 05W9 "standard pseudopullback cone from a right equivalence"]
def ofRightEquivalence
    (f : x ⟶ z) (hg : Bicategory.Equivalence.OnHom g) :
    PseudoPullbackCone f g :=
  (ofLeftEquivalence hg f).swap

/-- The standard cone for a right equivalence has the left source as its apex. -/
@[simp]
theorem ofRightEquivalence.pt
    (f : x ⟶ z) (hg : Bicategory.Equivalence.OnHom g) :
    (ofRightEquivalence f hg).pt = x := sorry

/-- The first projection of the standard cone for a right equivalence is the identity. -/
@[simp]
theorem ofRightEquivalence.fst
    (f : x ⟶ z) (hg : Bicategory.Equivalence.OnHom g) :
    (ofRightEquivalence f hg).fst = 𝟙 x := sorry

/-- The second projection of the standard cone for a right equivalence uses the chosen inverse. -/
@[simp]
theorem ofRightEquivalence.snd
    (f : x ⟶ z) (hg : Bicategory.Equivalence.OnHom g) :
    (ofRightEquivalence f hg).snd = f ≫ hg.inv := sorry

/-- The comparison isomorphism of the standard cone for a right equivalence is assembled from
the unitors, the chosen counit, and the inverse associator. -/
@[simp]
theorem ofRightEquivalence.iso
    (f : x ⟶ z) (hg : Bicategory.Equivalence.OnHom g) :
    (ofRightEquivalence f hg).iso =
      λ_ f ≪≫ (ρ_ f).symm ≪≫
        (Bicategory.whiskerLeftIso f hg.counit).symm ≪≫
          (α_ f hg.inv g).symm := sorry

/-- The standard right-equivalence cone is bilimit because it is the swap of the standard
left-equivalence bilimit cone. -/
@[stacks 05W9 "standard right-equivalence pseudopullback bilimit"]
instance ofRightEquivalence.isBilimit
    (f : x ⟶ z) (hg : Bicategory.Equivalence.OnHom g) :
    (ofRightEquivalence f hg).IsBilimit := sorry

/-- In a bilimit pseudopullback, equivalence data on the right cospan leg induce equivalence
data on the first projection. This is the second-projection equivalence of the swapped cone. -/
@[stacks 05W9 "pseudopullback first-projection equivalence"]
noncomputable def fstEquivalence
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hg : Bicategory.Equivalence.OnHom g) :
    Bicategory.Equivalence.OnHom P.fst :=
  sndEquivalence P.swap hg

namespace fstEquivalence

/-- The comparison isomorphism aligning the universal map from `P` to the standard right-leg
cone with the target first projection. This is the symmetric counterpart of
`sndEquivalence.homIso`. -/
noncomputable abbrev homIso
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hg : Bicategory.Equivalence.OnHom g) :
    (apexEquivalence P.swap (ofLeftEquivalence hg f)).hom ≅ P.fst :=
  sndEquivalence.homIso P.swap hg

/-- The forward cell of the symmetric first-projection alignment. -/
@[simp]
theorem homIso.hom
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hg : Bicategory.Equivalence.OnHom g) :
    (homIso P hg).hom =
      (sndEquivalence.homIso P.swap hg).hom := sorry

/-- The inverse cell of the symmetric first-projection alignment. -/
@[simp]
theorem homIso.inv
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hg : Bicategory.Equivalence.OnHom g) :
    (homIso P hg).inv =
      (sndEquivalence.homIso P.swap hg).inv := sorry

end fstEquivalence

/-- The inverse chosen for the first-projection equivalence is the reverse universal map from
the standard left-equivalence cone to the swapped input cone. -/
@[simp, stacks 05W9 "pseudopullback first-projection inverse readout"]
theorem fstEquivalence.inv
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hg : Bicategory.Equivalence.OnHom g) :
    (fstEquivalence P hg).inv =
      (apexEquivalence P.swap (ofLeftEquivalence hg f)).inv := sorry

/-- The unit selected for the first-projection equivalence is the unit of the swapped
second-projection equivalence. -/
@[simp]
theorem fstEquivalence.unit
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hg : Bicategory.Equivalence.OnHom g) :
    (fstEquivalence P hg).unit = (sndEquivalence P.swap hg).unit := sorry

/-- The counit selected for the first-projection equivalence is the counit of the swapped
second-projection equivalence. -/
@[simp]
theorem fstEquivalence.counit
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hg : Bicategory.Equivalence.OnHom g) :
    (fstEquivalence P hg).counit = (sndEquivalence P.swap hg).counit := sorry

/- Data audit (mathlib 4.32): `ofRightEquivalence` is exactly the explicit left standard cone
followed by the field-level involution `swap`; it selects no second apex, projection, or
comparison. `fstEquivalence` is exactly `sndEquivalence` on the swapped input, so it introduces
no inverse, unit, counit, or universal lift beyond the single left-direction owner. Deferred
content is confined to field readouts, bilimit transport, and coherence propositions. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
