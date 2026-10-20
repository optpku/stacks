module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.SndFiber.Equivalence

/-!
# Computation API for the costructured-arrow model of a second pseudo-pullback fibre

This leaf records stable formulas for the explicit unit, counit, quasi-inverse, and canonical
equivalence.
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

/-- The forward objectwise unit is the identity on the underlying left total object. -/
@[simp] theorem comparison.unitIso.app.hom.left
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    (comparison.unitIso.app F G f A).hom.left.1 = 𝟙 A.left.1 := sorry

/-- The inverse objectwise unit is the identity on the underlying left total object. -/
@[simp] theorem comparison.unitIso.app.inv.left
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    (comparison.unitIso.app F G f A).inv.left.1 = 𝟙 A.left.1 := sorry

/-- The packaged unit's forward component is the explicit objectwise unit map. -/
@[simp] theorem comparison.unitIso.hom.app
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    (comparison.unitIso F G f).hom.app A =
      (comparison.unitIso.app F G f A).hom := sorry

/-- The packaged unit's inverse component is the inverse explicit objectwise unit map. -/
@[simp] theorem comparison.unitIso.inv.app
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (A : costructuredArrow F G f) :
    (comparison.unitIso F G f).inv.app A =
      (comparison.unitIso.app F G f A).inv := sorry

/-- The base component of the forward counit is the endpoint transport from `f.left` to the
stored common base. -/
@[simp] theorem comparison.counitIso.app.hom.base
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    PseudoPullback.baseMap (comparison.counitIso.app F G f Q).hom.1 =
      eqToHom
        ((congrArg Over.left Q.2.symm).trans
          (PseudoPullback.fiberObj Q.1).snd.2) := sorry

/-- The first component of the forward counit is the identity of the retained first object. -/
@[simp] theorem comparison.counitIso.app.hom.fst
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    PseudoPullback.fstMap (comparison.counitIso.app F G f Q).hom.1 =
      𝟙 (PseudoPullback.fstObj Q.1) := sorry

/-- The second component of the forward counit is the endpoint transport from the fixed slice
object to the stored second component. -/
@[simp] theorem comparison.counitIso.app.hom.snd
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    PseudoPullback.sndMap (comparison.counitIso.app F G f Q).hom.1 =
      eqToHom Q.2.symm := sorry

/-- The base component of the inverse counit is the inverse endpoint transport. -/
@[simp] theorem comparison.counitIso.app.inv.base
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    PseudoPullback.baseMap (comparison.counitIso.app F G f Q).inv.1 =
      eqToHom
        ((congrArg Over.left Q.2.symm).trans
          (PseudoPullback.fiberObj Q.1).snd.2).symm := sorry

/-- The first component of the inverse counit is the identity of the retained first object. -/
@[simp] theorem comparison.counitIso.app.inv.fst
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    PseudoPullback.fstMap (comparison.counitIso.app F G f Q).inv.1 =
      𝟙 (PseudoPullback.fstObj Q.1) := sorry

/-- The second component of the inverse counit is the original outer-fibre endpoint transport. -/
@[simp] theorem comparison.counitIso.app.inv.snd
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    PseudoPullback.sndMap (comparison.counitIso.app F G f Q).inv.1 =
      eqToHom Q.2 := sorry

/-- The packaged counit's forward component is the explicit objectwise counit map. -/
@[simp] theorem comparison.counitIso.hom.app
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    (comparison.counitIso F G f).hom.app Q =
      (comparison.counitIso.app F G f Q).hom := sorry

/-- The packaged counit's inverse component is the inverse explicit objectwise counit map. -/
@[simp] theorem comparison.counitIso.inv.app
    [Functor.IsFibered.InGroupoids pY] (f : Over U)
    (Q : ((PseudoPullback.snd F G).toFunctor).Fiber f) :
    (comparison.counitIso F G f).inv.app Q =
      (comparison.counitIso.app F G f Q).inv := sorry

/-- The quasi-inverse stores the explicit inverse comparison functor. -/
@[simp] theorem comparison.quasiInverse.inverse
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.quasiInverse F G f).inverse = comparisonInverse F G f := sorry

/-- The quasi-inverse stores the named explicit unit. -/
@[simp] theorem comparison.quasiInverse.unitIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.quasiInverse F G f).unitIso = comparison.unitIso F G f := sorry

/-- The quasi-inverse stores the named explicit counit. -/
@[simp] theorem comparison.quasiInverse.counitIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.quasiInverse F G f).counitIso = comparison.counitIso F G f := sorry

/-- The functor of the canonical equivalence is the explicit costructured-arrow comparison. -/
@[simp]
theorem comparison.equivalence.functor
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.equivalence F G f).functor = comparison F G f := sorry

/-- The inverse of the canonical equivalence is the explicit fixed-second-fibre comparison. -/
@[simp]
theorem comparison.equivalence.inverse
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.equivalence F G f).inverse = comparisonInverse F G f := sorry

/-- The counit of the canonical equivalence is the named explicit reconstruction counit. -/
@[simp]
theorem comparison.equivalence.counitIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.equivalence F G f).counitIso = comparison.counitIso F G f := sorry

/-- The unit of the canonical equivalence is mathlib's adjointification of the named unit against
the named counit. -/
theorem comparison.equivalence.unitIso
    [Functor.IsFibered.InGroupoids pY] (f : Over U) :
    (comparison.equivalence F G f).unitIso =
      Equivalence.adjointifyη
        (CategoryTheory.BasedCategory.PseudoPullback.SndFiber.comparison.unitIso F G f)
        (CategoryTheory.BasedCategory.PseudoPullback.SndFiber.comparison.counitIso F G f) := sorry

end SndFiber
end BasedCategory.PseudoPullback

end CategoryTheory
