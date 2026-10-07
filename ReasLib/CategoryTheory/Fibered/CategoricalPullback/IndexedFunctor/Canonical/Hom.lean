module

public import ReasLib.CategoryTheory.Fibered.CategoricalPullback.IndexedFunctor.Canonical.Basic

/-!
# Hom transport for the canonical indexed pullback-fiber comparison

This leaf gives the computational boundary for restricted morphisms.  It
records both factorization through the change-of-cleavage indexed functor and
the usable conjugation formula, then packages the latter as a hom-set
equivalence for downstream transport arguments.
-/

@[expose] public section

open CategoryTheory.Limits
open CategoricalPullback
open scoped CategoricalPullback

universe uC uD uS vC vD vS

namespace CategoryTheory

open Functor Opposite
open scoped CategoryTheory.Bicategory

namespace Limits.CategoricalPullback

variable {C : Type uC} {D : Type uD} {S : Type uS}
variable [Category.{vC} C] [Category.{vD} D] [Category.{vS} S]

/-- Restricted-morphism transport for the canonical selected-cleavage comparison factors through
the canonical change from the independently selected pullback cleavage to the induced one. -/
theorem Indexed.canonical.functor.mapHom.factor
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      ((fiberPseudofunctor (π₁ u p)).map f₁.op.toLoc).toFunctor.obj X ⟶
        ((fiberPseudofunctor (π₁ u p)).map f₂.op.toLoc).toFunctor.obj Y) :
    (Indexed.canonical.functor u p).mapHom f₁ f₂ φ =
      (Indexed.chosen.functor u p).mapHom f₁ f₂
        ((Cleavage.Indexed.comparison
          (Cleavage.ofIsFibered (π₁ u p))
          (Cleavage.chosen u p)).mapHom f₁ f₂ φ) := sorry

/-- Restricted-morphism transport through the canonical pullback-fiber comparison is conjugation
by the two canonical restriction isomorphisms. -/
@[simp]
theorem Indexed.canonical.functor.mapHom
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      ((fiberPseudofunctor (π₁ u p)).map f₁.op.toLoc).toFunctor.obj X ⟶
        ((fiberPseudofunctor (π₁ u p)).map f₂.op.toLoc).toFunctor.obj Y) :
    (Indexed.canonical.functor u p).mapHom f₁ f₂ φ =
      (Indexed.canonical.comparisonIso u p f₁ X).inv ≫
        (Fiber.chosen.functor u p V).map φ ≫
        (Indexed.canonical.comparisonIso u p f₂ Y).hom := sorry

/-- Total-category readout of restricted-morphism transport through the canonical pullback-fiber
comparison. -/
theorem Indexed.canonical.functor.mapHom.toTotal
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      ((fiberPseudofunctor (π₁ u p)).map f₁.op.toLoc).toFunctor.obj X ⟶
        ((fiberPseudofunctor (π₁ u p)).map f₂.op.toLoc).toFunctor.obj Y) :
    ((Indexed.canonical.functor u p).mapHom f₁ f₂ φ).1 =
      (Indexed.canonical.comparisonIso u p f₁ X).inv.1 ≫
        ((Fiber.chosen.functor u p V).map φ).1 ≫
        (Indexed.canonical.comparisonIso u p f₂ Y).hom.1 := sorry

/-- The canonical selected-cleavage pullback-fiber comparison is an equivalence on every fiber. -/
instance Indexed.canonical.functor.fiberwiseEquivalence
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered] :
    (Indexed.canonical.functor u p).FiberwiseEquivalence := sorry

/-- The canonical pullback-fiber comparison identifies hom-sets between any two restricted
objects.  Its forward map is the canonical strictification conjugation. -/
noncomputable def Indexed.canonical.homEquiv
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂} :
    (((fiberPseudofunctor (π₁ u p)).map
        f₁.op.toLoc).toFunctor.obj X ⟶
      ((fiberPseudofunctor (π₁ u p)).map
        f₂.op.toLoc).toFunctor.obj Y) ≃
      (((fiberPseudofunctor p).map
        (u.map f₁).op.toLoc).toFunctor.obj
          ((Fiber.chosen.functor u p U₁).obj X) ⟶
      ((fiberPseudofunctor p).map
        (u.map f₂).op.toLoc).toFunctor.obj
          ((Fiber.chosen.functor u p U₂).obj Y)) :=
  (Indexed.canonical.functor u p).mapHomEquiv f₁ f₂

/-- The forward canonical restricted-hom equivalence is `mapHom`. -/
@[simp]
theorem Indexed.canonical.homEquiv.apply
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      ((fiberPseudofunctor (π₁ u p)).map f₁.op.toLoc).toFunctor.obj X ⟶
        ((fiberPseudofunctor (π₁ u p)).map f₂.op.toLoc).toFunctor.obj Y) :
    Indexed.canonical.homEquiv u p f₁ f₂ φ =
      (Indexed.canonical.functor u p).mapHom f₁ f₂ φ := sorry

/-- Applying the inverse canonical restricted-hom equivalence after strictification recovers the
original pullback-fiber morphism. -/
@[simp]
theorem Indexed.canonical.homEquiv.symm.apply
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (φ :
      ((fiberPseudofunctor (π₁ u p)).map f₁.op.toLoc).toFunctor.obj X ⟶
        ((fiberPseudofunctor (π₁ u p)).map f₂.op.toLoc).toFunctor.obj Y) :
    (Indexed.canonical.homEquiv u p f₁ f₂).symm
        ((Indexed.canonical.functor u p).mapHom f₁ f₂ φ) =
      φ := sorry

/-- Applying the canonical restricted-hom equivalence to an inverse image recovers the target
morphism. -/
@[simp]
theorem Indexed.canonical.homEquiv.apply.symm
    (u : C ⥤ D) (p : S ⥤ D) [p.IsFibered]
    {U₁ U₂ V : C} (f₁ : V ⟶ U₁) (f₂ : V ⟶ U₂)
    {X : (π₁ u p).Fiber U₁} {Y : (π₁ u p).Fiber U₂}
    (ψ :
      ((fiberPseudofunctor p).map
          (u.map f₁).op.toLoc).toFunctor.obj
            ((Fiber.chosen.functor u p U₁).obj X) ⟶
        ((fiberPseudofunctor p).map
          (u.map f₂).op.toLoc).toFunctor.obj
            ((Fiber.chosen.functor u p U₂).obj Y)) :
    Indexed.canonical.homEquiv u p f₁ f₂
        ((Indexed.canonical.homEquiv
          u p f₁ f₂).symm ψ) =
      ψ := sorry

end Limits.CategoricalPullback

end CategoryTheory
