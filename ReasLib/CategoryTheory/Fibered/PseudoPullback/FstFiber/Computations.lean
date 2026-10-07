module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.FstFiber.Equivalence

/-!
# Computation API for the structured-arrow model of a pseudo-pullback fibre

This leaf records stable projection formulas for the unit and counit, together with the
computation rules for the named quasi-inverse and canonical equivalence.
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

/-- The forward map of the objectwise unit is the identity on the underlying right total
object. -/
@[simp] theorem comparison.unitIso.app.hom.right
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : structuredArrow G F f) :
    (comparison.unitIso.app G F f A).hom.right.1 = 𝟙 A.right.1 := sorry

/-- The inverse map of the objectwise unit is the identity on the underlying right total
object. -/
@[simp] theorem comparison.unitIso.app.inv.right
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : structuredArrow G F f) :
    (comparison.unitIso.app G F f A).inv.right.1 = 𝟙 A.right.1 := sorry
/-- The forward component of the packaged unit is the explicit objectwise unit map. -/
@[simp] theorem comparison.unitIso.hom.app
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : structuredArrow G F f) :
    (comparison.unitIso G F f).hom.app A =
      (comparison.unitIso.app G F f A).hom := sorry

/-- The inverse component of the packaged unit is the inverse explicit objectwise unit map. -/
@[simp] theorem comparison.unitIso.inv.app
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : structuredArrow G F f) :
    (comparison.unitIso G F f).inv.app A =
      (comparison.unitIso.app G F f A).inv := sorry
/-- The base component of the forward objectwise counit is the canonical endpoint transport
from `f.left` to the stored common base. -/
@[simp] theorem comparison.counitIso.app.hom.base
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    PseudoPullback.baseMap (comparison.counitIso.app G F f Q).hom.1 =
      eqToHom
        ((congrArg Over.left Q.2.symm).trans
          (PseudoPullback.fiberObj Q.1).fst.2) := sorry

/-- The first component of the forward objectwise counit is the endpoint transport from the
fixed slice object to the stored first component. -/
@[simp] theorem comparison.counitIso.app.hom.fst
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    PseudoPullback.fstMap (comparison.counitIso.app G F f Q).hom.1 =
      eqToHom Q.2.symm := sorry

/-- The second component of the forward objectwise counit is the identity of the retained
second total object. -/
@[simp] theorem comparison.counitIso.app.hom.snd
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    PseudoPullback.sndMap (comparison.counitIso.app G F f Q).hom.1 =
      𝟙 (PseudoPullback.sndObj Q.1) := sorry

/-- The base component of the inverse objectwise counit is the inverse canonical endpoint
transport. -/
@[simp] theorem comparison.counitIso.app.inv.base
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    PseudoPullback.baseMap (comparison.counitIso.app G F f Q).inv.1 =
      eqToHom
        ((congrArg Over.left Q.2.symm).trans
          (PseudoPullback.fiberObj Q.1).fst.2).symm := sorry

/-- The first component of the inverse objectwise counit is the original outer-fibre endpoint
transport. -/
@[simp] theorem comparison.counitIso.app.inv.fst
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    PseudoPullback.fstMap (comparison.counitIso.app G F f Q).inv.1 =
      eqToHom Q.2 := sorry

/-- The second component of the inverse objectwise counit is the identity of the retained
second total object. -/
@[simp] theorem comparison.counitIso.app.inv.snd
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    PseudoPullback.sndMap (comparison.counitIso.app G F f Q).inv.1 =
      𝟙 (PseudoPullback.sndObj Q.1) := sorry
/-- The forward component of the packaged counit is the explicit objectwise counit map. -/
@[simp] theorem comparison.counitIso.hom.app
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    (comparison.counitIso G F f).hom.app Q =
      (comparison.counitIso.app G F f Q).hom := sorry

/-- The inverse component of the packaged counit is the inverse explicit objectwise counit
map. -/
@[simp] theorem comparison.counitIso.inv.app
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.fst G F).toFunctor).Fiber f) :
    (comparison.counitIso G F f).inv.app Q =
      (comparison.counitIso.app G F f Q).inv := sorry
/-- The inverse functor stored by the structured-arrow quasi-inverse is the explicit
forgetful construction. -/
@[simp] theorem comparison.quasiInverse.inverse
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.quasiInverse G F f).inverse = comparisonInverse G F f := sorry

/-- The unit stored by the structured-arrow quasi-inverse is the named explicit unit. -/
@[simp] theorem comparison.quasiInverse.unitIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.quasiInverse G F f).unitIso = comparison.unitIso G F f := sorry

/-- The counit stored by the structured-arrow quasi-inverse is the named explicit counit. -/
@[simp] theorem comparison.quasiInverse.counitIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.quasiInverse G F f).counitIso = comparison.counitIso G F f := sorry
/-- The functor of the canonical equivalence is the explicit structured-arrow-to-fiber functor.

Proof strategy: unfold `comparison.equivalence` and use
`Functor.QuasiInverse.adjointifyUnit.functor`. -/
@[simp]
theorem comparison.equivalence.functor
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.equivalence G F f).functor = comparison G F f := sorry

/-- The inverse of the canonical equivalence is the explicit fibre-to-structured-arrow
functor. -/
@[simp]
theorem comparison.equivalence.inverse
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.equivalence G F f).inverse = comparisonInverse G F f := sorry

/-- The counit of the canonical equivalence is the named explicit reconstruction counit. -/
@[simp]
theorem comparison.equivalence.counitIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.equivalence G F f).counitIso = comparison.counitIso G F f := sorry

/-- The unit of the canonical equivalence is mathlib's adjointification of the named explicit
unit against the named explicit counit. -/
theorem comparison.equivalence.unitIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.equivalence G F f).unitIso =
      Equivalence.adjointifyη
        (CategoryTheory.BasedCategory.PseudoPullback.FstFiber.comparison.unitIso G F f)
        (CategoryTheory.BasedCategory.PseudoPullback.FstFiber.comparison.counitIso G F f) := sorry

end FstFiber
end BasedCategory.PseudoPullback

end CategoryTheory
