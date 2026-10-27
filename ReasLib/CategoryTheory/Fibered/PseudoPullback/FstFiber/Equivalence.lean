/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.FstFiber.FromFiber
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
public import ReasLib.CategoryTheory.Functor.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence for the structured-arrow model of a pseudo-pullback fibre

This leaf assembles the explicit unit, counit, quasi-inverse data, equivalence instances, and
the canonical equivalence for the structured-arrow description of a fixed first fibre.
Projection-level and packaged-equivalence formulas are collected in `FstFiber.Computations`.
-/

@[expose] public section

universe uC vC uX vX uY vY

namespace CategoryTheory

open BasedCategory
open BasedFunctor
open Functor
open Functor.Fiber
open CategoryTheory.Limits
open Functor.IsHomLift

variable {C : Type uC} [Category.{vC} C]
variable {X : Type uX} [Category.{vX} X]
variable {Y : Type uY} [Category.{vY} Y]
variable {pX : X ⥤ C} {pY : Y ⥤ C}

namespace BasedCategory.PseudoPullback
namespace FstFiber

variable {U : C}
variable (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor pY)
variable (F : BasedCategory.ofFunctor pX ⥤ᵇ BasedCategory.ofFunctor pY)

section UnitImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The identity on the underlying right object is vertical when regarded as the forward map of
the unit's right-component isomorphism.

Proof strategy: normalize the transported fibre equality and apply `Functor.IsHomLift.id`. -/
private theorem unitRightHomIsHomLift
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : structuredArrow G F f) :
    pX.IsHomLift (𝟙 f.left) (𝟙 A.right.1) :=
  IsHomLift.id A.right.2

/-- The right-component isomorphism from a structured arrow to its reconstruction. Its
non-Prop payload is the identity isomorphism of the original total-category object; its forward
verticality witness is supplied and the inverse witness is inferred. -/
private noncomputable def unitRightIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : structuredArrow G F f) :
    A.right ≅ ((comparison G F f ⋙ comparisonInverse G F f).obj A).right :=
  Functor.Fiber.isoMk (Iso.refl A.right.1)
    (hhom := unitRightHomIsHomLift G F f A)

/-- The identity right-component isomorphism intertwines a structured arrow with its
reconstruction.

Proof strategy: apply `Functor.Fiber.hom_ext` and reduce the reconstructed comparison using
`comparison.obj.comparisonHom` and `comparisonInverse.obj.comparisonHom`. -/
private theorem unitTriangle
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : structuredArrow G F f) :
    A.hom ≫ (F.fiberFunctor f.left).map (unitRightIso G F f A).hom =
      ((comparison G F f ⋙ comparisonInverse G F f).obj A).hom := by
  apply Functor.Fiber.hom_ext
  change A.hom.1 ≫ F.toFunctor.map (𝟙 A.right.1) = 𝟙 _ ≫ A.hom.1
  exact (congrArg (fun k ↦ A.hom.1 ≫ k) (F.toFunctor.map_id A.right.1)).trans
    ((Category.comp_id _).trans (Category.id_comp _).symm)

end Implementation

/-- The objectwise unit from a structured arrow to the result of passing to the fixed first
fibre and back. The component is explicitly the identity on the underlying right object. -/
noncomputable def comparison.unitIso.app
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : structuredArrow G F f) :
    A ≅ (comparison G F f ⋙ comparisonInverse G F f).obj A :=
  StructuredArrow.isoMk (Implementation.unitRightIso G F f A)
    (Implementation.unitTriangle G F f A)

/-- The explicit objectwise unit components are natural in structured-arrow morphisms. -/
theorem comparison.unitIso.app.naturality
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B : structuredArrow G F f} (α : A ⟶ B) :
    α ≫ (comparison.unitIso.app G F f B).hom =
      (comparison.unitIso.app G F f A).hom ≫
        (comparison G F f ⋙ comparisonInverse G F f).map α := by
  apply StructuredArrow.hom_ext
  apply Functor.Fiber.hom_ext
  change α.right.1 ≫ 𝟙 B.right.1 = 𝟙 A.right.1 ≫ α.right.1
  simp only [Category.comp_id, Category.id_comp]

/-- The identity functor on structured arrows is naturally isomorphic to passage to the fixed
first fibre followed by the explicit inverse. -/
@[stacks 02Y5 "(1) unit of the structured-arrow comparison"]
noncomputable def comparison.unitIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    𝟭 (structuredArrow G F f) ≅
      comparison G F f ⋙ comparisonInverse G F f :=
  NatIso.ofComponents (comparison.unitIso.app G F f)
    (fun α ↦ comparison.unitIso.app.naturality G F f α)

end UnitImplementation

section CounitImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The base comparison from a reconstructed pseudo-pullback object to the original one. It is
the equality isomorphism obtained directly from the outer-fibre equality and the first
component's stored base equality. -/
private noncomputable def counitBaseIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    PseudoPullback.baseObj
        ((comparisonInverse G F f ⋙ comparison G F f).obj Q).1 ≅
      PseudoPullback.baseObj Q.1 :=
  eqToIso <|
    (congrArg Over.left Q.2.symm).trans
      (PseudoPullback.fiberObj Q.1).fst.2

/-- The first-component comparison from a reconstructed pseudo-pullback object to the original
one. It is the equality isomorphism supplied by the outer fibre, in the direction from the fixed
slice object back to the stored first component. -/
private noncomputable def counitFstIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    PseudoPullback.fstObj
        ((comparisonInverse G F f ⋙ comparison G F f).obj Q).1 ≅
      PseudoPullback.fstObj Q.1 :=
  eqToIso Q.2.symm

/-- The second-component comparison from a reconstructed pseudo-pullback object to the original
one. Its non-Prop payload is the identity isomorphism of the retained second total object. -/
private noncomputable def counitSndIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    PseudoPullback.sndObj
        ((comparisonInverse G F f ⋙ comparison G F f).obj Q).1 ≅
      PseudoPullback.sndObj Q.1 :=
  Iso.refl _

/-- The forward first-component comparison lies over the forward base comparison.

Proof strategy: unfold the two equality isomorphisms and use the defining base equality of the
slice object. -/
private theorem counitFstHomIsHomLift
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    (BasedCategory.ofFunctor (Over.forget U)).p.IsHomLift
      (counitBaseIso G F f Q).hom
      (counitFstIso G F f Q).hom := by
  apply IsHomLift.of_commsq _ _ _ rfl (PseudoPullback.fiberObj Q.1).fst.2
  change (Over.forget U).map (eqToHom Q.2.symm) ≫
    eqToHom (PseudoPullback.fiberObj Q.1).fst.2 =
      (𝟙 f.left) ≫ eqToHom
        ((congrArg Over.left Q.2.symm).trans (PseudoPullback.fiberObj Q.1).fst.2)
  rw [eqToHom_map, eqToHom_trans, Category.id_comp]
  rfl

/-- The forward identity second-component comparison lies over the forward base comparison.

Proof strategy: normalize the endpoint transports and use the stored second-component base
equality. -/
private theorem counitSndHomIsHomLift
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    (BasedCategory.ofFunctor pX).p.IsHomLift
      (counitBaseIso G F f Q).hom
      (counitSndIso G F f Q).hom := by
  exact IsHomLift.id_lift_eqToHom_codomain
    ((congrArg Over.left Q.2.symm).trans (PseudoPullback.fiberObj Q.1).fst.2)
    (PseudoPullback.fiberObj Q.1).snd.2

/-- The forward component comparisons intertwine the reconstructed and original
pseudo-pullback comparison maps.

Proof strategy: normalize the two equality transports and use the inverse law for the original
stored comparison isomorphism together with `comparisonInverse.obj.comparisonHom`. -/
private theorem counitComm
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    CommSq (G.toFunctor.map (counitFstIso G F f Q).hom)
      (PseudoPullback.comparison
        ((comparisonInverse G F f ⋙ comparison G F f).obj Q).1)
      (PseudoPullback.comparison Q.1) (F.toFunctor.map (counitSndIso G F f Q).hom) := by
  constructor
  change G.toFunctor.map (eqToHom Q.2.symm) ≫ PseudoPullback.comparison Q.1 =
    (eqToHom (congrArg G.toFunctor.obj Q.2.symm) ≫ PseudoPullback.comparison Q.1) ≫
      F.toFunctor.map (𝟙 (PseudoPullback.sndObj Q.1))
  rw [eqToHom_map G.toFunctor, F.toFunctor.map_id, Category.comp_id]

/-- The explicit total-category isomorphism from the reconstructed pseudo-pullback object to the
original one. Its base and first components are equality isomorphisms derived from input data,
and its second component is the identity; only lift and square laws are proof-valued. -/
private noncomputable def counitTotalIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    ((comparisonInverse G F f ⋙ comparison G F f).obj Q).1 ≅ Q.1 :=
  PseudoPullback.mkIso (counitBaseIso G F f Q)
    (counitFstIso G F f Q) (counitSndIso G F f Q)
    (hom_fst := counitFstHomIsHomLift G F f Q)
    (hom_snd := counitSndHomIsHomLift G F f Q)
    (counitComm G F f Q)

/-- The forward total comparison is vertical for the first projection.

Proof strategy: use `PseudoPullback.mkIso.hom.fstMap` and
`counitFstHomIsHomLift`, then rewrite the first projection through its based-functor
commutativity. -/
private theorem counitTotalIsoHomIsHomLift
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    (PseudoPullback.fst G F).toFunctor.IsHomLift
      (𝟙 f) (counitTotalIso G F f Q).hom := by
  apply IsHomLift.of_commsq _ _ _ rfl Q.2
  change eqToHom Q.2.symm ≫ eqToHom Q.2 = (𝟙 f) ≫ 𝟙 f
  simp only [eqToHom_trans, eqToHom_refl, Category.comp_id]
  rfl

end Implementation

/-- The objectwise counit from reconstruction back to the original object of the fixed first
fibre. It is assembled from explicit base, first-component, and identity second-component
isomorphisms, then packaged in the standard fibre. -/
noncomputable def comparison.counitIso.app
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    (comparisonInverse G F f ⋙ comparison G F f).obj Q ≅ Q :=
  Functor.Fiber.isoMk (Implementation.counitTotalIso G F f Q)
    (hhom := Implementation.counitTotalIsoHomIsHomLift G F f Q)

/-- The explicit objectwise counit components are natural in morphisms of the fixed first
fibre. -/
theorem comparison.counitIso.app.naturality
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {Q R : ((PseudoPullback.fst G F).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    (comparisonInverse G F f ⋙ comparison G F f).map α ≫
        (comparison.counitIso.app G F f R).hom =
      (comparison.counitIso.app G F f Q).hom ≫ α := by
  apply Functor.Fiber.hom_ext
  apply PseudoPullback.hom_ext
  · change (𝟙 f) ≫ eqToHom R.2.symm =
      eqToHom Q.2.symm ≫ PseudoPullback.fstMap α.1
    letI hα : (PseudoPullback.fst G F).toFunctor.IsHomLift (𝟙 f) α.1 := α.2
    have h := IsHomLift.fac' (PseudoPullback.fst G F).toFunctor (𝟙 f) α.1
    change PseudoPullback.fstMap α.1 =
      eqToHom Q.2 ≫ 𝟙 f ≫ eqToHom R.2.symm at h
    rw [h]
    erw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.id_comp]
  · change PseudoPullback.sndMap α.1 ≫ 𝟙 (PseudoPullback.sndObj R.1) =
      𝟙 (PseudoPullback.sndObj Q.1) ≫ PseudoPullback.sndMap α.1
    simp only [Category.comp_id, Category.id_comp]

/-- Passage from the fixed first fibre to structured arrows and back is naturally isomorphic to
the identity functor on that fibre. -/
@[stacks 02Y5 "(1) counit of the structured-arrow comparison"]
noncomputable def comparison.counitIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    comparisonInverse G F f ⋙ comparison G F f ≅
      𝟭 (((PseudoPullback.fst G F).toFunctor).Fiber f) :=
  NatIso.ofComponents (comparison.counitIso.app G F f)
    (fun α ↦ comparison.counitIso.app.naturality G F f α)

end CounitImplementation

/-- Explicit quasi-inverse data for the structured-arrow comparison functor. The inverse,
objectwise unit, and objectwise counit are all named constructions with projection-level
computation API. -/
@[stacks 02Y5 "(1) quasi-inverse for the structured-arrow comparison"]
noncomputable def comparison.quasiInverse
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    Functor.QuasiInverse (comparison G F f) where
  inverse := comparisonInverse G F f
  unitIso := comparison.unitIso G F f
  counitIso := comparison.counitIso G F f

/-- The fiber over `f : V ⟶ U` of
`(C/U) ×_Y X ⟶ C/U` is equivalent to the structured-arrow category whose objects are pairs
`(x, φ)` with `x ∈ X_V` and `φ : G(f) ⟶ F(x)` in `Y_V`.

Only the target projection `pY` must be fibered in groupoids: this makes each displayed
structured-arrow map `φ` invertible, as required by the pseudo-pullback object. No groupoid
condition on `pX` is used by the comparison.

Proof strategy: adjointify `comparison.quasiInverse G F f` and use mathlib's equivalence
instance for its forward functor. -/
instance comparison.isEquivalence
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison G F f).IsEquivalence :=
  (comparison.quasiInverse G F f).adjointifyUnit.isEquivalence_functor

/-- The explicit inverse functor is itself an equivalence whenever the forward
structured-arrow comparison is defined.

Proof strategy: adjointify `comparison.quasiInverse G F f` and use mathlib's equivalence
instance for its inverse functor. -/
instance comparisonInverse.isEquivalence
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparisonInverse G F f).IsEquivalence :=
  (comparison.quasiInverse G F f).adjointifyUnit.isEquivalence_inverse

/-- Lemma 4.42.1 (Stacks 02Y5) (1): the canonical equivalence between the structured-arrow
description and the first pseudo-pullback fibre. It is packaged from named explicit
quasi-inverse data, so both directions and both comparison isomorphisms remain available without
crossing a choice boundary. -/
@[stacks 02Y5 "(1)"]
noncomputable def comparison.equivalence
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    structuredArrow G F f ≌
      ((PseudoPullback.fst G F).toFunctor).Fiber f :=
  (comparison.quasiInverse G F f).adjointifyUnit

end FstFiber
end BasedCategory.PseudoPullback

end CategoryTheory
