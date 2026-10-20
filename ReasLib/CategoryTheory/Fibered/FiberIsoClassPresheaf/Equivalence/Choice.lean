module

public import ReasLib.CategoryTheory.Fibered.FiberIsoClassPresheaf.Equivalence.QuasiInverse

/-!
# Fiber-class presheaves from an equivalence property

This leaf specializes the explicit quasi-inverse comparison to the canonical
choice attached to `BasedFunctor.IsEquivalence`. The choice remains visible in
the inverse computation API, while the forward map depends only on the given
based functor.
-/

@[expose] public section

universe u v uX vX vY

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor.IsEquivalence

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uX} C}

/-- An equivalence over the base from a fibred category to a discrete fibration identifies the
source fibre-class presheaf with the target fibre-object presheaf. This property-level owner is
the canonical explicit comparison attached to `F.asQuasiInverse`. -/
noncomputable def fiberClassesIso
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [X.p.IsFibered] [Y.p.IsDiscreteFibration] :
    Functor.fiberIsoClassPresheaf X.p ≅ Y.p.fiberObjectPresheaf :=
  F.asQuasiInverse.fiberClassesIso

/-- The forward morphism of the property-level comparison is the canonical class-to-object map
attached to `F`; only the inverse uses the selected equivalence data. -/
@[simp]
theorem fiberClassesIso.hom_eq
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [X.p.IsFibered] [Y.p.IsDiscreteFibration] :
    (fiberClassesIso F).hom = BasedFunctor.fiberClassesMap F := sorry

/-- The inverse morphism of the property-level comparison is the inverse map
attached to the canonical quasi-inverse choice for `F`. -/
@[simp]
theorem fiberClassesIso.inv_eq
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [X.p.IsFibered] [Y.p.IsDiscreteFibration] :
    (fiberClassesIso F).inv = F.asQuasiInverse.fiberClassesInv := sorry

/-- On a represented source class, the presheaf comparison applies the induced fibre functor. -/
@[simp]
theorem fiberClassesIso.hom.app_mk
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [X.p.IsFibered] [Y.p.IsDiscreteFibration]
    (U : Cᵒᵖ) (x : X.p.Fiber (unop U)) :
    (fiberClassesIso F).hom.app U (Quotient.mk'' x) =
      (F.fiberFunctor (unop U)).obj x := sorry

/-- The inverse presheaf comparison takes the class of the image under the canonically chosen
inverse based functor. -/
@[simp]
theorem fiberClassesIso.inv.app
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [X.p.IsFibered] [Y.p.IsDiscreteFibration]
    (U : Cᵒᵖ) (y : Y.p.Fiber (unop U)) :
    (fiberClassesIso F).inv.app U y =
      Quotient.mk'' ((F.inv.fiberFunctor (unop U)).obj y) := sorry

/-- The property-level comparison agrees with the comparison built from any supplied explicit
quasi-inverse package. -/
theorem fiberClassesIso.eq_ofQuasiInverse
    (F : X ⥤ᵇ Y) [F.IsEquivalence] [X.p.IsFibered] [Y.p.IsDiscreteFibration]
    (e : BasedFunctor.QuasiInverse F) :
    fiberClassesIso F = e.fiberClassesIso := sorry

end BasedFunctor.IsEquivalence

end CategoryTheory
