/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Equivalence.Choice
public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Equivalence.QuasiInverse.ULift

/-!
# Universe-lifted fiber-class presheaves from an equivalence property

This leaf gives the heterogeneous-universe companion of the canonical
choice-based fiber-class presheaf comparison.
-/

@[expose] public section

universe w u v uX vX uY vY

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor.IsEquivalence

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}

/-- A base-preserving equivalence identifies fiber-class and fiber-object presheaves after a
chosen common universe lift. This is the heterogeneous-universe companion of
`BasedFunctor.IsEquivalence.fiberClassesIso`, obtained from the selected explicit
`F.asQuasiInverse` comparison. -/
noncomputable def fiberClassesIso.ulift
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [X.p.IsFibered] [Y.p.IsDiscreteFibration] :
    (Functor.fiberIsoClassPresheaf X.p ⋙
        (CategoryTheory.uliftFunctor.{max w uX uY, uX} :
          Type uX ⥤ Type (max w uX uY))) ≅
      (Y.p.fiberObjectPresheaf ⋙
        (CategoryTheory.uliftFunctor.{max w uX uY, uY} :
          Type uY ⥤ Type (max w uX uY))) :=
  BasedFunctor.QuasiInverse.fiberClassesIso.ulift.{w} F.asQuasiInverse

/-- The forward morphism of the lifted property-level comparison is the canonical lifted
class-to-object map attached to `F`. -/
@[simp]
theorem fiberClassesIso.ulift.hom_eq
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [X.p.IsFibered] [Y.p.IsDiscreteFibration] :
    (fiberClassesIso.ulift.{w} F).hom =
      BasedFunctor.fiberClassesMap.ulift.{w} F := sorry

/-- The inverse morphism of the lifted property-level comparison is the
lifted inverse map attached to the canonical quasi-inverse choice for `F`. -/
@[simp]
theorem fiberClassesIso.ulift.inv_eq
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [X.p.IsFibered] [Y.p.IsDiscreteFibration] :
    (fiberClassesIso.ulift.{w} F).inv =
      BasedFunctor.QuasiInverse.fiberClassesInv.ulift.{w} F.asQuasiInverse := sorry

/-- On a lifted represented source class, the comparison applies the induced fibre functor. -/
@[simp]
theorem fiberClassesIso.ulift.hom.app_mk
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [X.p.IsFibered] [Y.p.IsDiscreteFibration]
    (U : Cᵒᵖ) (x : X.p.Fiber (unop U)) :
    (fiberClassesIso.ulift.{w} F).hom.app U (ULift.up (Quotient.mk'' x)) =
      ULift.up ((F.fiberFunctor (unop U)).obj x) := sorry

/-- The inverse lifted comparison sends a target object to the lifted class of its image under
the canonically chosen inverse based functor. -/
@[simp]
theorem fiberClassesIso.ulift.inv.app
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [X.p.IsFibered] [Y.p.IsDiscreteFibration]
    (U : Cᵒᵖ) (y : Y.p.Fiber (unop U)) :
    (fiberClassesIso.ulift.{w} F).inv.app U (ULift.up y) =
      ULift.up (Quotient.mk'' ((F.inv.fiberFunctor (unop U)).obj y)) := sorry

/-- The property-level lifted comparison agrees with the lifted comparison built from any
supplied explicit quasi-inverse package. -/
theorem fiberClassesIso.ulift.eq_ofQuasiInverse
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [X.p.IsFibered] [Y.p.IsDiscreteFibration]
    (e : BasedFunctor.QuasiInverse F) :
    fiberClassesIso.ulift.{w} F =
      BasedFunctor.QuasiInverse.fiberClassesIso.ulift.{w} e := sorry

end BasedFunctor.IsEquivalence

end CategoryTheory
