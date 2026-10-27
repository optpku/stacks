/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.Equivalence.OnHom
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Equivalence

/-!
# Left-leg equivalences and pseudopullback projections

This directional leaf owns the standard bilimit pseudopullback cone associated to equivalence
data on the left cospan leg. Comparing an arbitrary bilimit cone with that standard cone gives
chosen adjoint-equivalence data on the second projection.

The construction is bicategorical: no stack, site, or fibered-category structure is used.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u

namespace CategoryTheory

open Bicategory

namespace Bicategory.PseudoPullbackCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {x y z : B} {f : x ⟶ z} {g : y ⟶ z}

/-- The standard pseudopullback cone of `f` and `g` when the left leg `f` is equipped with
equivalence data. Its apex is `y`, its second projection is the identity, and its first
projection uses the chosen inverse of `f`. -/
@[stacks 05W9 "standard pseudopullback cone from a left equivalence"]
def ofLeftEquivalence
    (hf : Bicategory.Equivalence.OnHom f) (g : y ⟶ z) :
    PseudoPullbackCone f g where
  pt := y
  fst := g ≫ hf.inv
  snd := 𝟙 y
  iso :=
    α_ g hf.inv f ≪≫
      Bicategory.whiskerLeftIso g hf.counit ≪≫
        ρ_ g ≪≫ (λ_ g).symm

/-- The standard cone for a left equivalence has the right source as its apex. -/
@[simp]
theorem ofLeftEquivalence.pt
    (hf : Bicategory.Equivalence.OnHom f) (g : y ⟶ z) :
    (ofLeftEquivalence hf g).pt = y := by
  rfl

/-- The first projection of the standard cone for a left equivalence uses the chosen inverse. -/
@[simp]
theorem ofLeftEquivalence.fst
    (hf : Bicategory.Equivalence.OnHom f) (g : y ⟶ z) :
    (ofLeftEquivalence hf g).fst = g ≫ hf.inv := by
  rfl

/-- The second projection of the standard cone for a left equivalence is the identity. -/
@[simp]
theorem ofLeftEquivalence.snd
    (hf : Bicategory.Equivalence.OnHom f) (g : y ⟶ z) :
    (ofLeftEquivalence hf g).snd = 𝟙 y := by
  rfl

/-- The comparison isomorphism of the standard cone for a left equivalence is assembled from
the associator, the chosen counit, and the unitors. -/
@[simp]
theorem ofLeftEquivalence.iso
    (hf : Bicategory.Equivalence.OnHom f) (g : y ⟶ z) :
    (ofLeftEquivalence hf g).iso =
      α_ g hf.inv f ≪≫
        Bicategory.whiskerLeftIso g hf.counit ≪≫
          ρ_ g ≪≫ (λ_ g).symm := by
  rfl

/-- The standard cone built from equivalence data on the left leg is a bilimit cone. -/
@[stacks 05W9 "standard left-equivalence pseudopullback bilimit"]
instance ofLeftEquivalence.isBilimit
    (hf : Bicategory.Equivalence.OnHom f) (g : y ⟶ z) :
    (ofLeftEquivalence hf g).IsBilimit := sorry

namespace sndEquivalence

/-- The comparison isomorphism aligning the universal map from `P` to the standard cone with
the target second projection. Naming this alignment keeps the chosen `unit` and `counit`
computations below independent of implementation `let` bindings. -/
noncomputable def homIso
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hf : Bicategory.Equivalence.OnHom f) :
    (apexEquivalence P (ofLeftEquivalence hf g)).hom ≅ P.snd :=
  (ρ_ (apexEquivalence P (ofLeftEquivalence hf g)).hom).symm ≪≫
    apexEquivalence.homSndIso P (ofLeftEquivalence hf g)

/-- The forward cell of the named second-projection alignment is the composite of the inverse
right unitor with the universal second-projection comparison. -/
@[simp]
theorem homIso.hom
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hf : Bicategory.Equivalence.OnHom f) :
    (homIso P hf).hom =
      (ρ_ (apexEquivalence P (ofLeftEquivalence hf g)).hom).inv ≫
        (apexEquivalence.homSndIso P (ofLeftEquivalence hf g)).hom := by
  rfl

/-- The inverse cell of the named second-projection alignment reverses the universal comparison
and then the right-unitor alignment. -/
@[simp]
theorem homIso.inv
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hf : Bicategory.Equivalence.OnHom f) :
    (homIso P hf).inv =
      (apexEquivalence.homSndIso P (ofLeftEquivalence hf g)).inv ≫
        (ρ_ (apexEquivalence P (ofLeftEquivalence hf g)).hom).hom := by
  rfl

end sndEquivalence

/-- In a bilimit pseudopullback, equivalence data on the left cospan leg induce equivalence
data on the second projection. -/
@[stacks 05W9 "pseudopullback second-projection equivalence"]
noncomputable def sndEquivalence
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hf : Bicategory.Equivalence.OnHom f) :
    Bicategory.Equivalence.OnHom P.snd :=
  let T := ofLeftEquivalence hf g
  let e : P.pt ≌ T.pt := apexEquivalence P T
  (Bicategory.Equivalence.OnHom.ofEquivalence e).changeHom
    (sndEquivalence.homIso P hf)

/-- The inverse chosen for the second-projection equivalence is the reverse universal map from
the standard cone. -/
@[simp, stacks 05W9 "pseudopullback second-projection inverse readout"]
theorem sndEquivalence.inv
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hf : Bicategory.Equivalence.OnHom f) :
    (sndEquivalence P hf).inv =
      (apexEquivalence P (ofLeftEquivalence hf g)).inv := by
  rfl

/-- The unit selected for the second-projection equivalence is the universal-apex unit
transported across the named projection alignment. -/
@[simp]
theorem sndEquivalence.unit
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hf : Bicategory.Equivalence.OnHom f) :
    (sndEquivalence P hf).unit =
      Bicategory.Equivalence.OnHom.changeHom.unitIso
        (Bicategory.Equivalence.OnHom.ofEquivalence
          (apexEquivalence P (ofLeftEquivalence hf g)))
        (sndEquivalence.homIso P hf) := by
  rfl

/-- The counit selected for the second-projection equivalence is the universal-apex counit
transported across the named projection alignment. -/
@[simp]
theorem sndEquivalence.counit
    (P : PseudoPullbackCone f g) [P.IsBilimit]
    (hf : Bicategory.Equivalence.OnHom f) :
    (sndEquivalence P hf).counit =
      Bicategory.Equivalence.OnHom.changeHom.counitIso
        (Bicategory.Equivalence.OnHom.ofEquivalence
          (apexEquivalence P (ofLeftEquivalence hf g)))
        (sndEquivalence.homIso P hf) := by
  rfl

/- Data audit (mathlib 4.32): `ofLeftEquivalence` stores its apex, projections, and comparison
isomorphism explicitly from the supplied `OnHom` data and bicategory coherence.
`sndEquivalence` reuses the canonical equivalence between bilimit apices and only changes its
forward morphism along the second-projection isomorphism. Its non-`Prop` inverse, unit, and
counit data introduce no new witness choice beyond the universal lift already owned by
`apexEquivalence`; deferred content is confined to bilimit and coherence propositions. -/

end Bicategory.PseudoPullbackCone

end CategoryTheory
