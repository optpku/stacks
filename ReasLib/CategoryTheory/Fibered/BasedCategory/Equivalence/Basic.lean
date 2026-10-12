/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Whiskering
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalences over a base

This module owns universe-polymorphic quasi-inverse data and the `BasedFunctor.IsEquivalence`
property, together with their elementary closure and strict-isomorphism bridges.
-/

@[expose] public section

namespace CategoryTheory

open BasedCategory
open BasedFunctor
open BasedNatTrans
open Functor.IsHomLift
open scoped Bicategory

universe u v uS uX uY vS vX vY

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- A heterogeneous-universe equivalence-over-base datum on a based functor. When source and
target lie in a common `BasedCategory` universe, this packages into the standard bicategorical
equivalence type in `Cat/C`. -/
structure QuasiInverse (F : X ⥤ᵇ Y) where
  /-- A based quasi-inverse to `F`. -/
  inverse : Y ⥤ᵇ X
  /-- The unit isomorphism of the equivalence over `C`. -/
  unitIso : 𝟭 X ≅ F ⋙ inverse
  /-- The counit isomorphism of the equivalence over `C`. -/
  counitIso : inverse ⋙ F ≅ 𝟭 Y

/-- A possibly universe-changing based functor is an equivalence over the base.

This is the property/typeclass layer analogous to `Functor.IsEquivalence`. Explicit inverse,
unit, and counit data are selected by `BasedFunctor.asQuasiInverse`; when source and target lie
in one `BasedCategory C` bicategory, `BasedFunctor.asEquivalence` packages the same property as
the canonical object `X ≌ Y`. -/
class IsEquivalence (F : X ⥤ᵇ Y) : Prop where
  /-- Explicit based quasi-inverse data merely exist; the property does not expose a choice. -/
  nonempty : Nonempty (QuasiInverse F)

namespace IsEquivalence

variable {F : X ⥤ᵇ Y}

/-- To prove that a based functor is an equivalence over the base, it suffices to provide a based
quasi-inverse together with based unit and counit isomorphisms. This mirrors
`Functor.IsEquivalence.mk'`. -/
protected theorem mk' (G : Y ⥤ᵇ X) (eta : 𝟭 X ≅ F ⋙ G) (eps : G ⋙ F ≅ 𝟭 Y) :
    F.IsEquivalence := sorry
/- Proof strategy: package `G`, `eta`, and `eps` as `QuasiInverse F`, introduce its
`Nonempty` witness, and then use the sole field of `BasedFunctor.IsEquivalence`. -/

end IsEquivalence

/-- Choose explicit quasi-inverse data for an equivalence over the base.

This is the heterogeneous-universe choice boundary corresponding to the inverse, unit, and
counit selected by `Functor.asEquivalence`. Consumers should use the projections of the returned
`QuasiInverse` rather than unfold this choice. -/
noncomputable def asQuasiInverse (F : X ⥤ᵇ Y) [F.IsEquivalence] : QuasiInverse F :=
  Classical.choice IsEquivalence.nonempty

/-- Choose explicit based quasi-inverse data from an ordinary proof of equivalence over the base.

This is the explicit-proof bridge to `BasedFunctor.asQuasiInverse`, not a second choice boundary.
It is useful when registering `h` as an ambient instance would create an overlapping typeclass
path. -/
noncomputable def asQuasiInverseOf (F : X ⥤ᵇ Y) (h : F.IsEquivalence) : QuasiInverse F :=
  @asQuasiInverse _ _ _ _ F h

/-- The chosen inverse based functor of an equivalence over the base. -/
noncomputable def inv (F : X ⥤ᵇ Y) [F.IsEquivalence] : Y ⥤ᵇ X :=
  F.asQuasiInverse.inverse

/-- The chosen unit isomorphism of an equivalence over the base. This is the stable projection
API for the choice encapsulated by `BasedFunctor.asQuasiInverse`. -/
noncomputable def unitIso (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    𝟭 X ≅ F ⋙ F.inv :=
  F.asQuasiInverse.unitIso

/-- The chosen counit isomorphism of an equivalence over the base. This is the stable projection
API for the choice encapsulated by `BasedFunctor.asQuasiInverse`. -/
noncomputable def counitIso (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    F.inv ⋙ F ≅ 𝟭 Y :=
  F.asQuasiInverse.counitIso

/-- The inverse projection of the chosen quasi-inverse data is the named chosen inverse. -/
@[simp]
theorem asQuasiInverse.inverse (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    F.asQuasiInverse.inverse = F.inv := sorry

/-- The unit projection of the chosen quasi-inverse data is the named chosen unit. -/
@[simp]
theorem asQuasiInverse.unitIso (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    F.asQuasiInverse.unitIso = F.unitIso := sorry

/-- The counit projection of the chosen quasi-inverse data is the named chosen counit. -/
@[simp]
theorem asQuasiInverse.counitIso (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    F.asQuasiInverse.counitIso = F.counitIso := sorry

/-- A based functor is an equivalence over the base exactly when explicit based quasi-inverse
data merely exist. -/
theorem isEquivalence_iff_nonempty_quasiInverse (F : X ⥤ᵇ Y) :
    F.IsEquivalence ↔ Nonempty (QuasiInverse F) := sorry

namespace QuasiInverse

variable {F : X ⥤ᵇ Y}

/-- Reverse explicit quasi-inverse data by swapping the forward and inverse functors and the
unit and counit isomorphisms. -/
def symm (e : QuasiInverse F) : QuasiInverse e.inverse where
  inverse := F
  unitIso := e.counitIso.symm
  counitIso := e.unitIso.symm

/-- Reversing explicit based quasi-inverse data selects the original forward functor as its
inverse. -/
@[simp]
theorem symm.inverse (e : QuasiInverse F) :
    e.symm.inverse = F := sorry

/-- Reversing explicit based quasi-inverse data uses the inverse counit as its unit. -/
@[simp]
theorem symm.unitIso (e : QuasiInverse F) :
    e.symm.unitIso = e.counitIso.symm := sorry

/-- Reversing explicit based quasi-inverse data uses the inverse unit as its counit. -/
@[simp]
theorem symm.counitIso (e : QuasiInverse F) :
    e.symm.counitIso = e.unitIso.symm := sorry

/-- Explicit quasi-inverse data exhibit the forward based functor as an equivalence over the
base. -/
theorem isEquivalence (e : QuasiInverse F) : F.IsEquivalence := sorry
/- Proof strategy: use `e` as the explicit witness of `Nonempty (QuasiInverse F)` in the
`IsEquivalence` constructor. -/

/-- The inverse based functors carried by two explicit quasi-inverses of the same based functor
are canonically isomorphic over the base. This is the choice-independence owner for constructions
that accept explicit based quasi-inverse data. -/
def inverseIso (e e' : QuasiInverse F) : e.inverse ≅ e'.inverse :=
  (eqToIso (BasedFunctor.comp_id e.inverse)).symm ≪≫
    BasedNatIso.whiskerLeft e.inverse e'.unitIso ≪≫
      (eqToIso (BasedFunctor.comp_assoc e.inverse F e'.inverse)).symm ≪≫
        BasedNatIso.whiskerRight e.counitIso e'.inverse ≪≫
          eqToIso (BasedFunctor.id_comp e'.inverse)

variable {Z : BasedCategory.{vS, uS} C} {G : Y ⥤ᵇ Z}

/-- The canonical unit isomorphism for the composite of explicit based quasi-inverse data. -/
def transUnitIso (e : QuasiInverse F) (f : QuasiInverse G) :
    𝟭 X ≅ (F ⋙ G) ⋙ (f.inverse ⋙ e.inverse) :=
  let middle : F ⋙ 𝟭 Y ≅ F ⋙ (G ⋙ f.inverse) :=
    BasedNatIso.mkNatIso
      (Functor.isoWhiskerLeft F.toFunctor
        ((BasedNatTrans.forgetful Y Y).mapIso f.unitIso))
      (BasedCategory.whiskerLeft F f.unitIso.hom).isHomLift'
  let h : F ≅ BasedFunctor.comp (BasedFunctor.comp F G) f.inverse :=
    (eqToIso (BasedFunctor.comp_id F)).symm ≪≫
      middle ≪≫
      (eqToIso (BasedFunctor.comp_assoc F G f.inverse)).symm
  let h' :
      BasedFunctor.comp F e.inverse ≅
        BasedFunctor.comp (BasedFunctor.comp (BasedFunctor.comp F G) f.inverse) e.inverse :=
    BasedNatIso.mkNatIso
      (Functor.isoWhiskerRight ((BasedNatTrans.forgetful X Y).mapIso h) e.inverse.toFunctor)
      (BasedCategory.whiskerRight h.hom e.inverse).isHomLift'
  e.unitIso ≪≫ h' ≪≫ eqToIso (BasedFunctor.comp_assoc (F ⋙ G) f.inverse e.inverse)

/-- The canonical counit isomorphism for the composite of explicit based quasi-inverse data. -/
def transCounitIso (e : QuasiInverse F) (f : QuasiInverse G) :
    (f.inverse ⋙ e.inverse) ⋙ (F ⋙ G) ≅ 𝟭 Z :=
  let middle : f.inverse ⋙ (e.inverse ⋙ F) ≅ f.inverse ⋙ 𝟭 Y :=
    BasedNatIso.mkNatIso
      (Functor.isoWhiskerLeft f.inverse.toFunctor
        ((BasedNatTrans.forgetful Y Y).mapIso e.counitIso))
      (BasedCategory.whiskerLeft f.inverse e.counitIso.hom).isHomLift'
  let h : BasedFunctor.comp (BasedFunctor.comp f.inverse e.inverse) F ≅ f.inverse :=
    eqToIso (BasedFunctor.comp_assoc f.inverse e.inverse F) ≪≫
      middle ≪≫
      eqToIso (BasedFunctor.comp_id f.inverse)
  let h' :
      BasedFunctor.comp (BasedFunctor.comp (BasedFunctor.comp f.inverse e.inverse) F) G ≅
        BasedFunctor.comp f.inverse G :=
    BasedNatIso.mkNatIso
      (Functor.isoWhiskerRight ((BasedNatTrans.forgetful Z Y).mapIso h) G.toFunctor)
      (BasedCategory.whiskerRight h.hom G).isHomLift'
  (eqToIso (BasedFunctor.comp_assoc (f.inverse ⋙ e.inverse) F G)).symm ≪≫ h' ≪≫ f.counitIso

/-- Explicit equivalence-over-base data compose. -/
def trans (e : QuasiInverse F) (f : QuasiInverse G) :
    QuasiInverse (F ⋙ G) where
  inverse := f.inverse ⋙ e.inverse
  unitIso := transUnitIso e f
  counitIso := transCounitIso e f

/-- The inverse in a composite of explicit based quasi-inverse data is the reverse composite of
the two inverses. -/
@[simp]
theorem trans.inverse (e : QuasiInverse F) (f : QuasiInverse G) :
    (e.trans f).inverse = f.inverse ⋙ e.inverse := sorry

/-- The unit in a composite of explicit based quasi-inverse data is the canonical composite
unit. -/
@[simp]
theorem trans.unitIso (e : QuasiInverse F) (f : QuasiInverse G) :
    (e.trans f).unitIso = transUnitIso e f := sorry

/-- The counit in a composite of explicit based quasi-inverse data is the canonical composite
counit. -/
@[simp]
theorem trans.counitIso (e : QuasiInverse F) (f : QuasiInverse G) :
    (e.trans f).counitIso = transCounitIso e f := sorry

end QuasiInverse

namespace IsEquivalence

variable {Z : BasedCategory.{vS, uS} C} {F : X ⥤ᵇ Y} {G : Y ⥤ᵇ Z}

/-- Equivalences over the base are closed under composition, including across heterogeneous
total-category universes. -/
theorem comp (hF : F.IsEquivalence) (hG : G.IsEquivalence) :
    (F ⋙ G).IsEquivalence := sorry
/- Proof strategy: choose the two encapsulated quasi-inverses, compose their explicit data with
`QuasiInverse.trans`, and package the result through `IsEquivalence.mk'` (or directly
through the class constructor). -/

end IsEquivalence

/-- The identity based functor is an equivalence over the base. -/
instance isEquivalence_refl (X : BasedCategory.{vX, uX} C) :
    (𝟭 X : X ⥤ᵇ X).IsEquivalence := sorry

/-- A composite of equivalences over the base is an equivalence over the base. -/
instance isEquivalence_trans
    {Z : BasedCategory.{vS, uS} C} (F : X ⥤ᵇ Y) (G : Y ⥤ᵇ Z)
    [F.IsEquivalence] [G.IsEquivalence] :
    (F ⋙ G).IsEquivalence := sorry

/-- The chosen inverse of an equivalence over the base is again an equivalence over the base. -/
instance isEquivalence_inv (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    F.inv.IsEquivalence := sorry
/- Proof strategy: reverse `F.asQuasiInverse` with `QuasiInverse.symm` and package the resulting
data with `QuasiInverse.isEquivalence`. -/

/-- Equivalence over the base is invariant under isomorphism of based functors. -/
theorem isEquivalence_of_iso
    {F G : X ⥤ᵇ Y} (e : F ≅ G) [F.IsEquivalence] :
    G.IsEquivalence := sorry
/- Proof strategy: keep `F.inv` and whisker the unit and counit selected for `F` by `e` and
`e.symm`, then apply `IsEquivalence.mk'`. -/

/-- Isomorphic based functors are simultaneously equivalences over the base. -/
theorem isEquivalence_iff_of_iso
    {F G : X ⥤ᵇ Y} (e : F ≅ G) :
    F.IsEquivalence ↔ G.IsEquivalence := sorry
/- Proof strategy: apply `isEquivalence_of_iso` to `e` and `e.symm`. -/

end BasedFunctor

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

/-- The equality-induced unit of a strict isomorphism is vertical over the base. -/
theorem BasedCategory.StrictIso.unitIsHomLift (e : BasedCategory.StrictIso X Y) (x : X.obj) :
    X.p.IsHomLift (𝟙 (X.p.obj x)) ((eqToIso e.toIsoCat.unit_eq).hom.app x) := sorry
/- Proof strategy: eliminate the strict functor equality `e.toIsoCat.unit_eq`; its component is
then an identity, and `Functor.IsHomLift.id` applies using the defining projection equality. -/

/-- The equality-induced counit of a strict isomorphism is vertical over the base. -/
theorem BasedCategory.StrictIso.counitIsHomLift (e : BasedCategory.StrictIso X Y) (y : Y.obj) :
    Y.p.IsHomLift (𝟙 (Y.p.obj y)) ((eqToIso e.toIsoCat.counit_eq).hom.app y) := sorry
/- Proof strategy: eliminate the strict functor equality `e.toIsoCat.counit_eq`; its component is
then an identity, and `Functor.IsHomLift.id` supplies the required verticality witness. -/

/-- A heterogeneous strict isomorphism over the base supplies explicit based quasi-inverse data.
The inverse is explicit, while the unit and counit are induced by the strict equations of the
underlying `IsoCat`. -/
def BasedCategory.StrictIso.toQuasiInverse (e : BasedCategory.StrictIso X Y) :
    BasedFunctor.QuasiInverse e.hom where
  inverse := e.inv
  unitIso := BasedNatIso.mkNatIso (eqToIso e.toIsoCat.unit_eq) e.unitIsHomLift
  counitIso := BasedNatIso.mkNatIso (eqToIso e.toIsoCat.counit_eq) e.counitIsHomLift

/-- The forward based functor of a strict isomorphism is automatically an equivalence. -/
def BasedCategory.StrictIso.homIsEquivalence (e : BasedCategory.StrictIso X Y) :
    e.hom.IsEquivalence :=
  e.toQuasiInverse.isEquivalence

/-- The inverse based functor of a strict isomorphism is automatically an equivalence. -/
def BasedCategory.StrictIso.invIsEquivalence (e : BasedCategory.StrictIso X Y) :
    e.inv.IsEquivalence :=
  e.toQuasiInverse.symm.isEquivalence

/- Axiom audit: the inverse and the underlying unit/counit natural isomorphisms come explicitly
from `e`. Any `sorryAx` is confined to the `IsHomLift` proof fields supplied by
`unitIsHomLift` and `counitIsHomLift`; no carrier, functor, component, or inverse component is
selected by a placeholder. -/

end CategoryTheory
