/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.SndFiber.FromFiber
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
public import ReasLib.CategoryTheory.Functor.Equivalence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Equivalence for the costructured-arrow model of a second pseudo-pullback fibre

This leaf assembles explicit unit, counit, quasi-inverse data, and the canonical equivalence for
the costructured-arrow description of a fixed second fibre.
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
namespace SndFiber

variable {U : C}
variable (F : BasedCategory.ofFunctor pX ⥤ᵇ BasedCategory.ofFunctor pY)
variable (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ BasedCategory.ofFunctor pY)

section UnitImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The identity on the underlying left object is vertical as the unit's forward component. -/
private theorem unitLeftHomIsHomLift
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    pX.IsHomLift (𝟙 f.left) (𝟙 A.left.1) := sorry

/-- The left-component isomorphism from a costructured arrow to its reconstruction. -/
private noncomputable def unitLeftIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    A.left ≅ ((comparison F G f ⋙ comparisonInverse F G f).obj A).left :=
  Functor.Fiber.isoMk (Iso.refl A.left.1)
    (hhom := unitLeftHomIsHomLift F G f A)

/-- The identity left-component isomorphism intertwines a costructured arrow with its
reconstruction. -/
private theorem unitTriangle
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    (F.fiberFunctor f.left).map (unitLeftIso F G f A).hom ≫
        ((comparison F G f ⋙ comparisonInverse F G f).obj A).hom =
      A.hom := sorry

end Implementation

/-- The objectwise unit from a costructured arrow to passage through the fixed second fibre and
back. Its non-Prop component is the identity isomorphism on the underlying left object. -/
noncomputable def comparison.unitIso.app
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    A ≅ (comparison F G f ⋙ comparisonInverse F G f).obj A :=
  CostructuredArrow.isoMk (Implementation.unitLeftIso F G f A)
    (Implementation.unitTriangle F G f A)

/-- The explicit objectwise unit components are natural. -/
theorem comparison.unitIso.app.naturality
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {A B : costructuredArrow F G f} (α : A ⟶ B) :
    α ≫ (comparison.unitIso.app F G f B).hom =
      (comparison.unitIso.app F G f A).hom ≫
        (comparison F G f ⋙ comparisonInverse F G f).map α := sorry

/-- The identity on costructured arrows is naturally isomorphic to comparison followed by its
explicit inverse. -/
@[stacks 02Y5 "(1) formal dual unit of the costructured-arrow comparison"]
noncomputable def comparison.unitIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    𝟭 (costructuredArrow F G f) ≅
      comparison F G f ⋙ comparisonInverse F G f :=
  NatIso.ofComponents (comparison.unitIso.app F G f)
    (fun α ↦ comparison.unitIso.app.naturality F G f α)

end UnitImplementation

section CounitImplementation

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

/-- The base isomorphism from a reconstructed object to the original second-fibre object. -/
private noncomputable def counitBaseIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    PseudoPullback.baseObj
        ((comparisonInverse F G f ⋙ comparison F G f).obj Q).1 ≅
      PseudoPullback.baseObj Q.1 :=
  eqToIso <|
    (congrArg Over.left Q.2.symm).trans
      (PseudoPullback.fiberObj Q.1).snd.2

/-- The first-component counit isomorphism retains the original first total object. -/
private noncomputable def counitFstIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    PseudoPullback.fstObj
        ((comparisonInverse F G f ⋙ comparison F G f).obj Q).1 ≅
      PseudoPullback.fstObj Q.1 :=
  Iso.refl _

/-- The second-component counit isomorphism is the endpoint transport from `f` to the stored
second object. -/
private noncomputable def counitSndIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    PseudoPullback.sndObj
        ((comparisonInverse F G f ⋙ comparison F G f).obj Q).1 ≅
      PseudoPullback.sndObj Q.1 :=
  eqToIso Q.2.symm

/-- The identity first-component comparison lies over the base endpoint transport. -/
private theorem counitFstHomIsHomLift
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    (BasedCategory.ofFunctor pX).p.IsHomLift
      (counitBaseIso F G f Q).hom
      (counitFstIso F G f Q).hom := sorry

/-- The second-component endpoint transport lies over the base endpoint transport. -/
private theorem counitSndHomIsHomLift
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    (BasedCategory.ofFunctor (Over.forget U)).p.IsHomLift
      (counitBaseIso F G f Q).hom
      (counitSndIso F G f Q).hom := sorry

/-- The counit component isomorphisms intertwine the reconstructed and original comparisons. -/
private theorem counitComm
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    CommSq (F.toFunctor.map (counitFstIso F G f Q).hom)
      (PseudoPullback.comparison
        ((comparisonInverse F G f ⋙ comparison F G f).obj Q).1)
      (PseudoPullback.comparison Q.1)
      (G.toFunctor.map (counitSndIso F G f Q).hom) := sorry

/-- The explicit total-category counit isomorphism. Its first component is retained and its
second component is the endpoint transport supplied by the outer fibre. -/
private noncomputable def counitTotalIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    ((comparisonInverse F G f ⋙ comparison F G f).obj Q).1 ≅ Q.1 :=
  PseudoPullback.mkIso (counitBaseIso F G f Q)
    (counitFstIso F G f Q) (counitSndIso F G f Q)
    (hom_fst := counitFstHomIsHomLift F G f Q)
    (hom_snd := counitSndHomIsHomLift F G f Q)
    (counitComm F G f Q)

/-- The forward total counit comparison is vertical for the second projection. -/
private theorem counitTotalIsoHomIsHomLift
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    (PseudoPullback.snd F G).toFunctor.IsHomLift
      (𝟙 f) (counitTotalIso F G f Q).hom := sorry

end Implementation

/-- The objectwise counit from reconstruction to the original fixed-second-fibre object. -/
noncomputable def comparison.counitIso.app
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    (comparisonInverse F G f ⋙ comparison F G f).obj Q ≅ Q :=
  Functor.Fiber.isoMk (Implementation.counitTotalIso F G f Q)
    (hhom := Implementation.counitTotalIsoHomIsHomLift F G f Q)

/-- The explicit objectwise counit components are natural. -/
theorem comparison.counitIso.app.naturality
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    {Q R : ((PseudoPullback.snd F G).toFunctor).Fiber f}
    (α : Q ⟶ R) :
    (comparisonInverse F G f ⋙ comparison F G f).map α ≫
        (comparison.counitIso.app F G f R).hom =
      (comparison.counitIso.app F G f Q).hom ≫ α := sorry

/-- Passage from the fixed second fibre to costructured arrows and back is naturally isomorphic
to the identity. -/
@[stacks 02Y5 "(1) formal dual counit of the costructured-arrow comparison"]
noncomputable def comparison.counitIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    comparisonInverse F G f ⋙ comparison F G f ≅
      𝟭 (((PseudoPullback.snd F G).toFunctor).Fiber f) :=
  NatIso.ofComponents (comparison.counitIso.app F G f)
    (fun α ↦ comparison.counitIso.app.naturality F G f α)

end CounitImplementation

/-- Explicit quasi-inverse data for the costructured-arrow comparison. -/
@[stacks 02Y5 "(1) formal dual quasi-inverse for the costructured-arrow comparison"]
noncomputable def comparison.quasiInverse
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    Functor.QuasiInverse (comparison F G f) where
  inverse := comparisonInverse F G f
  unitIso := comparison.unitIso F G f
  counitIso := comparison.counitIso F G f

/-- The costructured-arrow comparison is an equivalence. -/
@[stacks 02Y5 "(1) formal dual comparison equivalence instance"]
instance comparison.isEquivalence
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison F G f).IsEquivalence := sorry

/-- The explicit inverse comparison is an equivalence. -/
@[stacks 02Y5 "(1) formal dual inverse comparison equivalence instance"]
instance comparisonInverse.isEquivalence
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparisonInverse F G f).IsEquivalence := sorry

/-- The canonical equivalence between the costructured-arrow description and the fixed second
pseudo-pullback fibre. -/
@[stacks 02Y5 "(1) formal dual"]
noncomputable def comparison.equivalence
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    costructuredArrow F G f ≌
      ((PseudoPullback.snd F G).toFunctor).Fiber f :=
  (comparison.quasiInverse F G f).adjointifyUnit

end SndFiber
end BasedCategory.PseudoPullback

end CategoryTheory
