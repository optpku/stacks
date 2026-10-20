/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.Basic
public import ReasLib.CategoryTheory.Fibered.InGroupoids
public import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Fiber characterizations of discrete fibrations

This file relates the intrinsic unique-lift owner to fibredness in groupoids and strict
discreteness of the standard fibers.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂ uB vB

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor

namespace IsDiscreteFibration

/-- A discrete fibration is canonically fibred in groupoids.

Proof strategy: use unique lifts to prove that every chosen lift is strongly Cartesian, then apply
`Functor.IsFibered.of_exists_isStronglyCartesian`. Comparing an arbitrary total morphism with
the unique lift of its image proves that it is Cartesian. -/
@[stacks 0043 "a discrete fibration is fibred in groupoids"]
theorem toInGroupoids {p : S ⥤ C} (h : Functor.IsDiscreteFibration p) :
    Functor.IsFibered.InGroupoids p := by
  letI := h
  exact {
    toIsFibered := IsFibered.of_exists_isStronglyCartesian (fun a R f ↦
      ⟨(lift p f).domain, (lift p f).hom, lift.isStronglyCartesian p f⟩)
    all_isCartesian := fun φ ↦
      letI := IsHomLift.isStronglyCartesian (p := p) (IsHomLift.map φ)
      IsStronglyCartesian.isCartesian_of_isStronglyCartesian p (p.map φ) φ
  }

/-- A discrete fibration is faithful: two arrows with the same image are two
lifts of the same base arrow with a common codomain, hence coincide by lift
uniqueness. -/
@[stacks 0043 "a discrete fibration is faithful"]
instance faithful (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    p.Faithful := sorry

/-- Typeclass-search form of
`Functor.IsDiscreteFibration.toInGroupoids`. -/
@[stacks 0043 "discrete-fibration groupoid instance"]
instance inGroupoids (p : S ⥤ C) [Functor.IsDiscreteFibration p] :
    Functor.IsFibered.InGroupoids p :=
  toInGroupoids inferInstance

/-- Every standard fiber of a discrete fibration is a strictly
discrete category.

Proof strategy: a fiber morphism and the identity of its codomain both package as lifts of the
same base identity. Lift subsingletonity identifies the packages, hence their domain objects and
morphisms. These equalities provide `IsDiscrete.eq_of_hom` and the subsingleton hom-spaces. -/
@[stacks 04TM "the standard fibres are discrete"]
instance fiberIsDiscrete (p : S ⥤ C) [Functor.IsDiscreteFibration p] (U : C) :
    IsDiscrete (p.Fiber U) := sorry

end IsDiscreteFibration

/-- Cartesian factorization compares any two lifts by a vertical map. Strict discreteness
of the standard fiber identifies their domain objects and their morphisms. -/
private theorem homLift_subsingleton_of_isFibered_fibersDiscrete
    (p : S ⥤ C) (hp : p.IsFibered) (hfiber : ∀ U : C, IsDiscrete (p.Fiber U))
    {R : C} {a : S} (f : R ⟶ p.obj a) : Subsingleton (HomLift p f) := sorry

/-- Fiberedness together with strictly discrete standard fibers constructs a discrete fibration.
The lift object and arrow are the native Cartesian pullback supplied by `hp`; fiber discreteness
is used only for the uniqueness law. -/
theorem IsDiscreteFibration.of_isFibered_fibersDiscrete
    (p : S ⥤ C) (hp : p.IsFibered) (hfiber : ∀ U : C, IsDiscrete (p.Fiber U)) :
    Functor.IsDiscreteFibration p := by
  letI := hp
  exact {
    homLiftNonempty := fun f ↦ ⟨{
      domain := IsPreFibered.pullbackObj (p := p) rfl f
      hom := IsPreFibered.pullbackMap (p := p) rfl f
      isHomLift := inferInstance
    }⟩
    homLiftSubsingleton := fun f ↦ homLift_subsingleton_of_isFibered_fibersDiscrete p hp hfiber f
  }

/-- The unique-lift owner is exactly the source's formulation: a category fibred in groupoids
whose standard fibers are strictly discrete.

Proof strategy: the forward implication uses the canonical superclass and fiber instances above.
The reverse implication retains the supplied fibredness and its actual Cartesian lifts. -/
theorem IsDiscreteFibration.iff_inGroupoids_fibersDiscrete (p : S ⥤ C) :
    Functor.IsDiscreteFibration p ↔
      Functor.IsFibered.InGroupoids p ∧ ∀ U : C, IsDiscrete (p.Fiber U) := by
  constructor
  · intro hp
    letI := hp
    exact ⟨IsDiscreteFibration.toInGroupoids hp, fun U ↦ inferInstance⟩
  · rintro ⟨hp, hfiber⟩
    exact IsDiscreteFibration.of_isFibered_fibersDiscrete p hp.toIsFibered hfiber

/-- A functor is a discrete fibration exactly when it is fibered and all its standard fibers are
strictly discrete.

The reverse direction uses the same explicit Cartesian lift constructor as the groupoid
characterization. -/
theorem IsDiscreteFibration.iff_isFibered_fibersDiscrete (p : S ⥤ C) :
    Functor.IsDiscreteFibration p ↔ p.IsFibered ∧ ∀ U : C, IsDiscrete (p.Fiber U) := by
  constructor
  · intro hp
    letI := hp
    exact ⟨(IsDiscreteFibration.toInGroupoids hp).toIsFibered, fun U ↦ inferInstance⟩
  · rintro ⟨hp, hfiber⟩
    exact IsDiscreteFibration.of_isFibered_fibersDiscrete p hp hfiber

/-- A lift through a composite projects to the same lift through its second factor. -/
private theorem isHomLift_map_of_comp
    {B : Type uB} [Category.{vB} B] (F : S ⥤ B) (G : B ⥤ C)
    {R T : C} {a b : S} {f : R ⟶ T} {φ : a ⟶ b}
    (hφ : (F ⋙ G).IsHomLift f φ) : G.IsHomLift f (F.map φ) := by
  cases hφ
  exact IsHomLift.map _

/-- A supplied lift remains a lift after applying the second base functor. -/
private theorem isHomLift_comp_of_lift
    {B : Type uB} [Category.{vB} B] (F : S ⥤ B) (G : B ⥤ C)
    {R T : B} {a b : S} {f : R ⟶ T} {φ : a ⟶ b}
    (hφ : F.IsHomLift f φ) : (F ⋙ G).IsHomLift (G.map f) φ := by
  cases hφ
  exact IsHomLift.map _

/-- Strict uniqueness in the second discrete fibration reflects the actual lifted arrow. -/
private theorem isHomLift_of_comp_discreteFibration
    {B : Type uB} [Category.{vB} B] (F : S ⥤ B) (G : B ⥤ C)
    [G.IsDiscreteFibration] {R : B} {a b : S} (f : R ⟶ F.obj b) (φ : a ⟶ b)
    (hφ : (F ⋙ G).IsHomLift (G.map f) φ) : F.IsHomLift f φ := by
  let projected : HomLift G (G.map f) :=
    ⟨F.obj a, F.map φ, isHomLift_map_of_comp F G hφ⟩
  let requested : HomLift G (G.map f) := ⟨R, f, IsHomLift.map f⟩
  have e : projected = requested := (IsDiscreteFibration.homLiftSubsingleton (G.map f)).elim _ _
  have h : F.IsHomLift projected.hom φ := IsHomLift.map φ
  rw [e] at h
  exact h

/-- The strong Cartesian factor is the given composite's native factor map; discrete lift
uniqueness reflects its image to the requested intermediate base arrow. -/
private theorem isStronglyCartesian_of_comp_discreteFibration
    {B : Type uB} [Category.{vB} B] (F : S ⥤ B) (G : B ⥤ C)
    [G.IsDiscreteFibration] {R : B} {a b : S} (f : R ⟶ F.obj b) (φ : a ⟶ b)
    [(F ⋙ G).IsStronglyCartesian (G.map f) φ] : F.IsStronglyCartesian f φ := by
  have hφ : F.IsHomLift f φ := isHomLift_of_comp_discreteFibration F G f φ inferInstance
  letI : F.IsHomLift f φ := hφ
  have ha : F.obj a = R := IsHomLift.domain_eq F f φ
  cases ha
  refine { toIsHomLift := hφ, universal_property' := ?_ }
  intro a' g φ' hφ'
  letI : (F ⋙ G).IsHomLift (G.map (g ≫ f)) φ' :=
    isHomLift_comp_of_lift F G hφ'
  let χ := IsStronglyCartesian.map (F ⋙ G) (G.map f) φ (G.map_comp g f) φ'
  refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
  · exact isHomLift_of_comp_discreteFibration F G g χ inferInstance
  · exact IsStronglyCartesian.fac (F ⋙ G) (G.map f) φ (G.map_comp g f) φ'
  · intro ψ hψ
    letI : F.IsHomLift g ψ := hψ.1
    letI : (F ⋙ G).IsHomLift (G.map g) ψ := isHomLift_comp_of_lift F G hψ.1
    exact IsStronglyCartesian.map_uniq (F ⋙ G) (G.map f) φ
      (G.map_comp g f) φ' ψ hψ.2

/-- Fibredness of a composite reflects to its first factor when the second factor is a
discrete fibration. The actual Cartesian lift is taken from the supplied composite fibredness. -/
theorem IsFibered.of_comp_of_discreteFibration
    {B : Type uB} [Category.{vB} B]
    (F : S ⥤ B) (G : B ⥤ C) [G.IsDiscreteFibration]
    [(F ⋙ G).IsFibered] : F.IsFibered := by
  apply IsFibered.of_exists_isStronglyCartesian
  intro a R f
  let φ := IsPreFibered.pullbackMap (p := F ⋙ G) rfl (G.map f)
  letI : (F ⋙ G).IsCartesian (G.map f) φ :=
    IsPreFibered.pullbackMap.IsCartesian (p := F ⋙ G) rfl (G.map f)
  letI : (F ⋙ G).IsStronglyCartesian (G.map f) φ :=
    IsFibered.isStronglyCartesian_of_isCartesian (F ⋙ G) (G.map f) φ
  exact ⟨IsPreFibered.pullbackObj (p := F ⋙ G) rfl (G.map f), φ,
    isStronglyCartesian_of_comp_discreteFibration F G f φ⟩

end Functor

end CategoryTheory
