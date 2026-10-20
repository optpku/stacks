module

public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.TypeValued.Over

/-!
# Fibers at localized site points

This module compares the fiber at a point of a slice site with the fiber at
the ambient point.  The comparison is independent of the choice of
coefficients: it applies to every target category with the colimits used by a
point fiber.
-/

@[expose] public section

open CategoryTheory.Limits Opposite

universe u v w a b

noncomputable section

namespace CategoryTheory.GrothendieckTopology.Point.OverFiber

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]
variable {A : Type a} [Category.{b} A] [HasColimitsOfSize.{w, w} A]

/-- The colimit comparison for the fiber of a presheaf after localizing a point at
`x : p.fiber.obj U`.  Restriction along `Over.forget U`, followed by the fiber at `p.over x`,
computes the original fiber at `p`. -/
noncomputable def presheafObjIso
    (p : GrothendieckTopology.Point.{w} J) {U : C} (x : p.fiber.obj U) (P : Cᵒᵖ ⥤ A) :
    (p.over x).presheafFiber.obj ((Over.forget U).op ⋙ P) ≅ p.presheafFiber.obj P := by
  let e := FunctorToTypes.FromOverFunctor.elementsEquivalence p.fiber x
  let t :=
    (p.presheafFiberCocone P).whisker (Over.forget (p.fiber.elementsMk U x)).op
  have ht : IsColimit t :=
    (Functor.Final.isColimitWhiskerEquiv
      (Over.forget (p.fiber.elementsMk U x)).op (p.presheafFiberCocone P)).symm
      (p.isColimitPresheafFiberCocone P)
  have ht' : IsColimit (t.whisker e.functor.op) :=
    (Functor.Final.isColimitWhiskerEquiv e.functor.op t).symm ht
  let c := (p.over x).isColimitPresheafFiberCocone ((Over.forget U).op ⋙ P)
  simpa [e, t, FunctorToTypes.FromOverFunctor.elementsEquivalence] using
    IsColimit.coconePointUniqueUpToIso c ht'

/-- The localized presheaf-fiber comparison sends each canonical localized generator to the
corresponding canonical generator of the ambient fiber. -/
@[simp]
theorem presheafObjIso_hom_fac
    (p : GrothendieckTopology.Point.{w} J) {U : C} (x : p.fiber.obj U) (P : Cᵒᵖ ⥤ A)
    (V : Over U) (y : (p.over x).fiber.obj V) :
    (p.over x).toPresheafFiber V y ((Over.forget U).op ⋙ P) ≫
        (presheafObjIso p x P).hom =
      p.toPresheafFiber V.left y.1 P := sorry

/-- The objectwise localized presheaf-fiber comparisons are natural in the presheaf. -/
theorem presheafObjIso_naturality
    (p : GrothendieckTopology.Point.{w} J) {U : C} (x : p.fiber.obj U)
    {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (p.over x).presheafFiber.map ((Over.forget U).op.whiskerLeft f) ≫
        (presheafObjIso p x Q).hom =
      (presheafObjIso p x P).hom ≫ p.presheafFiber.map f := sorry

/-- Restriction to the slice site, followed by the localized presheaf fiber, is naturally
isomorphic to the original presheaf fiber. -/
noncomputable def presheafIso
    (p : GrothendieckTopology.Point.{w} J) {U : C} (x : p.fiber.obj U) :
    (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ A).obj (Over.forget U).op ⋙
        (p.over x).presheafFiber ≅
      p.presheafFiber :=
  NatIso.ofComponents (fun P ↦ presheafObjIso p x P)
    (fun f ↦ presheafObjIso_naturality p x f)

/-- Restriction to `C / U`, followed by the fiber at the localized point `p.over x`, is naturally
isomorphic to the fiber at `p` on sheaves with arbitrary coefficients. -/
noncomputable def sheafIso
    (p : GrothendieckTopology.Point.{w} J) {U : C} (x : p.fiber.obj U) :
    J.overPullback A U ⋙ (p.over x).sheafFiber ≅ p.sheafFiber := by
  change
    (((Over.forget U).sheafPushforwardContinuous A (J.over U) J ⋙
        sheafToPresheaf (J.over U) A) ⋙ (p.over x).presheafFiber) ≅
      (sheafToPresheaf J A ⋙ p.presheafFiber)
  exact
    Functor.associator
      ((Over.forget U).sheafPushforwardContinuous A (J.over U) J)
      (sheafToPresheaf (J.over U) A) ((p.over x).presheafFiber) ≪≫
    Functor.isoWhiskerRight
      ((Over.forget U).sheafPushforwardContinuousCompSheafToPresheafIso A (J.over U) J)
      ((p.over x).presheafFiber) ≪≫
    (Functor.associator (sheafToPresheaf J A)
      ((Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ A).obj (Over.forget U).op)
      ((p.over x).presheafFiber)).symm ≪≫
    Functor.isoWhiskerLeft (sheafToPresheaf J A) (presheafIso p x)

/-- The objectwise form of `sheafIso`, expressed using the canonical slice sheaf `F.over U`. -/
noncomputable def sheafObjIso
    (p : GrothendieckTopology.Point.{w} J) {U : C} (x : p.fiber.obj U) (F : Sheaf J A) :
    (p.over x).sheafFiber.obj (F.over U) ≅ p.sheafFiber.obj F := by
  simpa [Sheaf.over, GrothendieckTopology.overPullback] using (sheafIso p x).app F

end CategoryTheory.GrothendieckTopology.Point.OverFiber
