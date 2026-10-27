/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Maps
import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.Maps
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects.Construction
public import ReasLib.CategoryTheory.Fibered.Stack.InSetoids
public import ReasLib.CategoryTheory.Fibered.Stack.Over
public import ReasLib.CategoryTheory.Fibered.Stack.Prestack
import Mathlib.Tactic.CrossRefAttribute

/-!
# Inertia objects of stacks

Closure of relative and absolute inertia under the stack conditions, and the corresponding
bundled `StackOver` objects. Computations comparing these owners with neutral fibered-category
owners are isolated in `Basic.Comparisons`.
-/

@[expose] public section

universe u v uX vX uY vY w vS

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace BasedCategory.Inertia

/-- Absolute inertia preserves the stack-on-site condition for an arbitrary based category
with fibred projection. -/
@[stacks 036Y "absolute inertia stack closure for based categories"]
theorem isStackOnSite
    (X : BasedCategory.{vS, w} C) [IsStack.OnSite J X.p] :
    IsStack.OnSite J (BasedCategory.inertia X).p := sorry

end BasedCategory.Inertia

namespace BasedCategory.RelativeInertia

variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}

/-- Lemma 8.7.1 (1), relative part, tag 036Y, in the heterogeneous cartesian layer: relative
inertia is a stack when its source is a stack and its target is a prestack. -/
@[stacks 036Y "heterogeneous relative-inertia stack closure"]
theorem isStackOnSite
    [IsStack.OnSite J X.p] [IsPrestack.OnSite J Y.p]
    (F : CartesianBasedFunctor X.p Y.p) :
    IsStack.OnSite J (BasedCategory.relativeInertia F.toBasedFunctor).p := sorry

/-- Cartesian factorization in the source lifts to relative inertia: uniqueness forces the
factor to intertwine the vertical automorphisms. -/
theorem isCartesian [Functor.IsFibered.InGroupoids X.p]
    (F : X ⥤ᵇ Y) {A B : CategoryTheory.RelativeInertia F.toFunctor} (φ : A ⟶ B) :
    (BasedCategory.relativeInertia F).p.IsCartesian
      ((BasedCategory.relativeInertia F).p.map φ) φ := by
  let p := (BasedCategory.relativeInertia F).p
  have lift_iff {A B : CategoryTheory.RelativeInertia F.toFunctor}
      {U V : C} (f : U ⟶ V) (ψ : A ⟶ B) :
      p.IsHomLift f ψ ↔ X.p.IsHomLift f (CategoryTheory.RelativeInertia.hom ψ) := by
    constructor
    · intro h
      letI := h
      exact IsHomLift.of_fac X.p f (CategoryTheory.RelativeInertia.hom ψ)
        (IsHomLift.domain_eq p f ψ)
        (IsHomLift.codomain_eq p f ψ)
        (IsHomLift.fac p f ψ)
    · intro h
      letI := h
      exact IsHomLift.of_fac p f ψ
        (@IsHomLift.domain_eq C X.obj _ _ X.p U V A.obj B.obj f
          (CategoryTheory.RelativeInertia.hom ψ) h)
        (@IsHomLift.codomain_eq C X.obj _ _ X.p U V A.obj B.obj f
          (CategoryTheory.RelativeInertia.hom ψ) h)
        (@IsHomLift.fac C X.obj _ _ X.p U V A.obj B.obj f
          (CategoryTheory.RelativeInertia.hom ψ) h)
  have vertical (A : CategoryTheory.RelativeInertia F.toFunctor) :
      X.p.IsHomLift (𝟙 (X.p.obj A.obj)) A.aut.hom := by
    have h : X.p.map A.aut.hom = 𝟙 (X.p.obj A.obj) := by
      rw [← F.w]
      change Y.p.map (F.toFunctor.map A.aut.hom) = 𝟙 _
      rw [show F.toFunctor.map A.aut.hom = 𝟙 _ from congrArg Iso.hom A.property,
        Y.p.map_id]
    rw [← h]
    infer_instance
  refine { universal_property := ?_ }
  intro Z ψ hψ
  letI : X.p.IsHomLift (X.p.map (CategoryTheory.RelativeInertia.hom φ))
      (CategoryTheory.RelativeInertia.hom ψ) := (lift_iff _ ψ).mp hψ
  obtain ⟨χ, ⟨hχ, hfac⟩, huniq⟩ :=
    Functor.IsCartesian.universal_property (p := X.p)
      (f := X.p.map (CategoryTheory.RelativeInertia.hom φ))
      (φ := CategoryTheory.RelativeInertia.hom φ) (CategoryTheory.RelativeInertia.hom ψ)
  letI := hχ
  letI := vertical A
  have hZ := IsHomLift.domain_eq X.p (𝟙 (X.p.obj A.obj)) χ
  letI : X.p.IsHomLift (𝟙 (X.p.obj A.obj)) Z.aut.hom := by
    rw [← hZ]
    exact vertical Z
  have hcomm : Z.aut.hom ≫ χ = χ ≫ A.aut.hom := by
    apply Functor.IsCartesian.ext X.p
      (X.p.map (CategoryTheory.RelativeInertia.hom φ)) (CategoryTheory.RelativeInertia.hom φ)
    calc
      (Z.aut.hom ≫ χ) ≫ CategoryTheory.RelativeInertia.hom φ =
          Z.aut.hom ≫ CategoryTheory.RelativeInertia.hom ψ := by
        rw [Category.assoc, hfac]
      _ = CategoryTheory.RelativeInertia.hom ψ ≫ B.aut.hom := ψ.hom.property
      _ = (χ ≫ CategoryTheory.RelativeInertia.hom φ) ≫ B.aut.hom := by rw [hfac]
      _ = χ ≫ (A.aut.hom ≫ CategoryTheory.RelativeInertia.hom φ) := by
        rw [φ.hom.property, Category.assoc]
      _ = (χ ≫ A.aut.hom) ≫ CategoryTheory.RelativeInertia.hom φ :=
        (Category.assoc _ _ _).symm
  refine ⟨CategoryTheory.RelativeInertia.homMk F.toFunctor χ hcomm,
    ⟨(lift_iff _ _).mpr hχ, ?_⟩, ?_⟩
  · apply InducedCategory.hom_ext
    apply Subtype.ext
    exact hfac
  · intro δ hδ
    apply InducedCategory.hom_ext
    apply Subtype.ext
    apply huniq
    exact ⟨(lift_iff _ _).mp hδ.1,
      congrArg (fun τ : Z ⟶ B => CategoryTheory.RelativeInertia.hom τ) hδ.2⟩

/-- Lemma 8.7.1 (2), relative part, tag 036Y, in the heterogeneous cartesian layer: relative
inertia is a stack in groupoids when its source is one and its target is a prestack. -/
@[stacks 036Y "heterogeneous relative-inertia groupoid closure"]
theorem isStackInGroupoids
    [IsStack.InGroupoids J X.p] [IsPrestack.OnSite J Y.p]
    (F : CartesianBasedFunctor X.p Y.p) :
    IsStack.InGroupoids J (BasedCategory.relativeInertia F.toBasedFunctor).p := by
  have h := isStackOnSite (J := J) F
  exact
    { toInGroupoids :=
        { toIsFibered := h.toIsFibered
          all_isCartesian := fun φ => isCartesian (X := X) (Y := Y) F.toBasedFunctor φ }
      toIsStack := h.toIsStack }

/-- Lemma 8.7.1 (3), relative part, tag 036Y, in the heterogeneous cartesian layer: relative
inertia is a stack in setoids when its source is one and its target is a prestack. -/
@[stacks 036Y "heterogeneous relative-inertia setoid closure"]
theorem isStackInSetoids
    [IsStack.InSetoids J X.p] [IsPrestack.OnSite J Y.p]
    (F : CartesianBasedFunctor X.p Y.p) :
    IsStack.InSetoids J (BasedCategory.relativeInertia F.toBasedFunctor).p := by
  letI : IsStack.InGroupoids J X.p :=
    { toInGroupoids := inferInstance
      toIsStack := inferInstance }
  have h := isStackInGroupoids (J := J) F
  exact
    { toInSetoids :=
        { toInGroupoids := h.toInGroupoids
          toFaithful := ⟨by
            intro A B φ ψ hφψ
            apply InducedCategory.hom_ext
            apply Subtype.ext
            exact X.p.map_injective hφψ⟩ }
      toIsStack := h.toIsStack }

end BasedCategory.RelativeInertia

namespace FiberedCategoryOver.RelativeInertia

variable {X Y : FiberedCategoryOver.{u, v, w, vS} C}

/-- Fixed-universe specialization of heterogeneous relative-inertia stack closure. -/
@[stacks 036Y "fixed-universe relative-inertia stack closure"]
theorem isStackOnSite
    [IsStack.OnSite J X.p] [IsPrestack.OnSite J Y.p] (F : X ⟶ Y) :
    IsStack.OnSite J (FiberedCategoryOver.relativeInertia F).p := by
  exact BasedCategory.RelativeInertia.isStackOnSite (J := J)
    (FiberedCategoryOver.toCartesianBasedFunctor F)

/-- Fixed-universe specialization of heterogeneous relative-inertia groupoid-stack closure. -/
@[stacks 036Y "fixed-universe relative-inertia groupoid closure"]
theorem isStackInGroupoids
    [IsStack.InGroupoids J X.p] [IsPrestack.OnSite J Y.p] (F : X ⟶ Y) :
    IsStack.InGroupoids J (FiberedCategoryOver.relativeInertia F).p := by
  exact BasedCategory.RelativeInertia.isStackInGroupoids (J := J)
    (FiberedCategoryOver.toCartesianBasedFunctor F)

/-- Fixed-universe specialization of heterogeneous relative-inertia setoid-stack closure. -/
@[stacks 036Y "fixed-universe relative-inertia setoid closure"]
theorem isStackInSetoids
    [IsStack.InSetoids J X.p] [IsPrestack.OnSite J Y.p] (F : X ⟶ Y) :
    IsStack.InSetoids J (FiberedCategoryOver.relativeInertia F).p := by
  exact BasedCategory.RelativeInertia.isStackInSetoids (J := J)
    (FiberedCategoryOver.toCartesianBasedFunctor F)

end FiberedCategoryOver.RelativeInertia

namespace FiberedCategoryOver.Inertia

/-- Absolute inertia preserves the stack-on-site condition. -/
@[stacks 036Y "fixed-universe absolute inertia stack closure"]
theorem isStackOnSite
    (X : FiberedCategoryOver.{u, v, w, vS} C) [IsStack.OnSite J X.p] :
    IsStack.OnSite J (FiberedCategoryOver.inertia X).p := by
  exact BasedCategory.Inertia.isStackOnSite (J := J) X.toBasedCategory

/-- Absolute inertia preserves stacks in groupoids. -/
@[stacks 036Y "fixed-universe absolute inertia groupoid closure"]
theorem isStackInGroupoids
    (X : FiberedCategoryOver.{u, v, w, vS} C) [IsStack.InGroupoids J X.p] :
    IsStack.InGroupoids J (FiberedCategoryOver.inertia X).p := by
  have h := isStackOnSite (J := J) X
  exact
    { toInGroupoids :=
        { toIsFibered := h.toIsFibered
          all_isCartesian := fun φ =>
            BasedCategory.RelativeInertia.isCartesian (X := X.toBasedCategory)
              X.toBasedCategory.toBase φ }
      toIsStack := h.toIsStack }

/-- Absolute inertia preserves stacks in setoids. -/
@[stacks 036Y "fixed-universe absolute inertia setoid closure"]
theorem isStackInSetoids
    (X : FiberedCategoryOver.{u, v, w, vS} C) [IsStack.InSetoids J X.p] :
    IsStack.InSetoids J (FiberedCategoryOver.inertia X).p := by
  letI : IsStack.InGroupoids J X.p :=
    { toInGroupoids := inferInstance
      toIsStack := inferInstance }
  have h := isStackInGroupoids (J := J) X
  exact
    { toInSetoids :=
        { toInGroupoids := h.toInGroupoids
          toFaithful := ⟨by
            intro A B φ ψ hφψ
            apply InducedCategory.hom_ext
            apply Subtype.ext
            exact X.p.map_injective hφψ⟩ }
      toIsStack := h.toIsStack }

end FiberedCategoryOver.Inertia

namespace StackOver

variable {X Y : StackOver.{u, v, w, vS} J}

/-- The relative inertia of a morphism of stacks, bundled again as a stack over the same site. -/
@[stacks 036Y "relative inertia stack"]
def relativeInertia (F : X ⟶ Y) : StackOver.{u, v, max w vS, vS} J :=
  StackOver.mk
    (FiberedCategoryOver.relativeInertia (StackOver.Hom.toMor F))
    (FiberedCategoryOver.RelativeInertia.isStackOnSite
      (J := J) (StackOver.Hom.toMor F))

/-- The absolute inertia of a stack, bundled again as a stack over the same site. -/
@[stacks 036Y "absolute inertia stack"]
def inertia (X : StackOver.{u, v, w, vS} J) : StackOver.{u, v, max w vS, vS} J :=
  StackOver.mk
    (FiberedCategoryOver.inertia X.toFiberedCategoryOver)
    (FiberedCategoryOver.Inertia.isStackOnSite (J := J) X.toFiberedCategoryOver)

end StackOver

end CategoryTheory
