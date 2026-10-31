/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Groupoid.InFunctors.Pointwise

/-!
# Representable groupoids in functors

A representable groupoid in functors on `C` is given by objects `U`, `R` of `C`, morphisms
`s, t : U ⟶ R`, a pushout of `s` and `t`, and a morphism `c : R ⟶ pushout s t` such that
the coyoneda quintuple is a groupoid in functors.
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe u v

noncomputable section

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

namespace Representable

/-- Composition of `T`-points of `R` induced by `c : R ⟶ pushout s t`. -/
def compApp {U R : C} (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    {T : C} (a b : R ⟶ T) (h : s ≫ a = t ≫ b) : R ⟶ T :=
  c ≫ pushout.desc a b h

/-- The coyoneda interpretation of object-level source is precomposition with `s`. -/
theorem coyoneda_map_src_app {U R : C} (s : U ⟶ R) {T : C} (a : R ⟶ T) :
    (coyoneda.map s.op).app T a = s ≫ a :=
  rfl

/-- The coyoneda quintuple of `U`, `R`, `s`, `t`, `c` is a groupoid in functors. -/
abbrev isCoyonedaGroupoid {U R : C} (s t : U ⟶ R) [HasPushout s t]
    (c : R ⟶ pushout s t) : Prop :=
  IsGroupoidInFunctors (coyoneda.obj (op U)) (coyoneda.obj (op R))
    (coyoneda.map s.op) (coyoneda.map t.op) (compApp s t c)

/-- The source of a composite `T`-point is the source of the earlier arrow.
This is the groupoid source law, available only when the coyoneda quintuple is a
groupoid in functors; equivalently `s ≫ c = s ≫ pushout.inr s t`. -/
theorem compApp_src {U R : C} (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    [h_groupoid : isCoyonedaGroupoid s t c] {T : C} (a b : R ⟶ T)
    (h : s ≫ a = t ≫ b) :
    s ≫ compApp s t c a b h = s ≫ b :=
  by exact h_groupoid.comp_src a b h

/-- The target of a composite `T`-point is the target of the later arrow.
This is the groupoid target law, available only when the coyoneda quintuple is a
groupoid in functors; equivalently `t ≫ c = t ≫ pushout.inl s t`. -/
theorem compApp_tgt {U R : C} (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    [h_groupoid : isCoyonedaGroupoid s t c] {T : C} (a b : R ⟶ T)
    (h : s ≫ a = t ≫ b) :
    t ≫ compApp s t c a b h = t ≫ a :=
  by exact h_groupoid.comp_tgt a b h

/-- Object-level source law of composition: postcomposing `c` with `s` recovers the
earlier-arrow inclusion of the pushout. -/
theorem source_comp {U R : C} (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    [h_groupoid : isCoyonedaGroupoid s t c] :
    s ≫ c = s ≫ pushout.inr s t :=
  by
    have h := compApp_src s t c (pushout.inl s t) (pushout.inr s t) (pushout.condition :
      s ≫ pushout.inl s t = t ≫ pushout.inr s t)
    rw [compApp, pushout.desc_inl_inr, Category.comp_id] at h
    exact h

/-- Object-level target law of composition: postcomposing `c` with `t` recovers the
later-arrow inclusion of the pushout. -/
theorem target_comp {U R : C} (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    [h_groupoid : isCoyonedaGroupoid s t c] :
    t ≫ c = t ≫ pushout.inl s t :=
  by
    have h := compApp_tgt s t c (pushout.inl s t) (pushout.inr s t) (pushout.condition :
      s ≫ pushout.inl s t = t ≫ pushout.inr s t)
    rw [compApp, pushout.desc_inl_inr, Category.comp_id] at h
    exact h

end Representable

/-- A representable groupoid in functors on `C`, given by objects `U`, `R`, morphisms
`s, t : U ⟶ R`, a chosen pushout of `s` and `t`, and composition `c`. -/
structure Representable (C : Type u) [Category.{v} C] where
  /-- The object representing the functor of objects. -/
  U : C
  /-- The object representing the functor of arrows. -/
  R : C
  /-- The object-level source morphism. -/
  s : U ⟶ R
  /-- The object-level target morphism. -/
  t : U ⟶ R
  /-- The pushout `R ⨿_{s, U, t} R` exists. -/
  [hasPushout : HasPushout s t]
  /-- Object-level composition, as a morphism into the pushout. -/
  c : R ⟶ pushout s t
  /-- The coyoneda quintuple is a groupoid in functors on `C`. -/
  isGroupoid : Representable.isCoyonedaGroupoid s t c

attribute [instance] Representable.hasPushout Representable.isGroupoid

namespace Representable

variable {C : Type u} [Category.{v} C]

/-- The coyoneda functor of objects `coyoneda.obj (op G.U)`. -/
abbrev functorU (G : Representable C) : C ⥤ Type v :=
  coyoneda.obj (op G.U)

/-- The coyoneda functor of arrows `coyoneda.obj (op G.R)`. -/
abbrev functorR (G : Representable C) : C ⥤ Type v :=
  coyoneda.obj (op G.R)

/-- The functor-level source `coyoneda.map G.s.op : functorR G ⟶ functorU G`. -/
abbrev functorSrc (G : Representable C) : G.functorR ⟶ G.functorU :=
  coyoneda.map G.s.op

/-- The functor-level target `coyoneda.map G.t.op : functorR G ⟶ functorU G`. -/
abbrev functorTgt (G : Representable C) : G.functorR ⟶ G.functorU :=
  coyoneda.map G.t.op

/-- Package objects, source, target, composition, and the groupoid laws. -/
def of (U R : C) (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    (h : isCoyonedaGroupoid s t c) : Representable C where
  U := U
  R := R
  s := s
  t := t
  c := c
  isGroupoid := h

/-- The object representing objects in a packaged representable groupoid is the supplied `U`. -/
theorem of_U (U R : C) (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    (h : isCoyonedaGroupoid s t c) : (of U R s t c h).U = U :=
  rfl

/-- The object representing arrows in a packaged representable groupoid is the supplied `R`. -/
theorem of_R (U R : C) (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    (h : isCoyonedaGroupoid s t c) : (of U R s t c h).R = R :=
  rfl

/-- The source morphism of a packaged representable groupoid is the supplied `s`. -/
theorem of_s (U R : C) (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    (h : isCoyonedaGroupoid s t c) : (of U R s t c h).s = s :=
  rfl

/-- The target morphism of a packaged representable groupoid is the supplied `t`. -/
theorem of_t (U R : C) (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    (h : isCoyonedaGroupoid s t c) : (of U R s t c h).t = t :=
  rfl

/-- The composition morphism of a packaged representable groupoid is the supplied `c`. -/
theorem of_c (U R : C) (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    (h : isCoyonedaGroupoid s t c) : (of U R s t c h).c = c :=
  rfl

/-- The discrete representable groupoid in functors on an object `U`. -/
def discrete (U : C) : Representable C where
  U := U
  R := U
  s := 𝟙 U
  t := 𝟙 U
  c := pushout.inl (𝟙 U) (𝟙 U)
  isGroupoid := by
    refine
      { comp_src := ?_
        comp_tgt := ?_
        assoc := ?_
        exists_id := ?_
        exists_inv := ?_
        naturality := ?_ }
    · intro T a b h
      change (𝟙 U ≫ a) = (𝟙 U ≫ b) at h
      change 𝟙 U ≫ compApp (𝟙 U) (𝟙 U) (pushout.inl (𝟙 U) (𝟙 U)) a b h =
        𝟙 U ≫ b
      simpa only [compApp, pushout.inl_desc, Category.id_comp] using h
    · intro T a b h
      change (𝟙 U ≫ a) = (𝟙 U ≫ b) at h
      change 𝟙 U ≫ compApp (𝟙 U) (𝟙 U) (pushout.inl (𝟙 U) (𝟙 U)) a b h =
        𝟙 U ≫ a
      simp only [compApp, pushout.inl_desc, Category.id_comp]
    · intro T a b d h_ab h_bd h_ab_d h_a_bd
      simp only [compApp, pushout.inl_desc]
    · intro T x
      refine ⟨x, ?_, ?_, ?_, ?_⟩
      · change 𝟙 U ≫ x = x
        simp only [Category.id_comp]
      · change 𝟙 U ≫ x = x
        simp only [Category.id_comp]
      · intro a h
        change 𝟙 U ≫ a = 𝟙 U ≫ x at h
        rw [compApp, pushout.inl_desc]
      · intro a h
        change 𝟙 U ≫ x = 𝟙 U ≫ a at h
        have h' : x = a := by simpa only [Category.id_comp] using h
        rw [compApp, pushout.inl_desc, h']
    · intro T a
      refine ⟨a, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · intro b h
        rw [compApp, pushout.inl_desc]
      · intro b h
        have h' : a = b := by
          simpa only [coyoneda_map_src_app, compApp, pushout.inl_desc,
            Category.id_comp] using h
        simpa only [compApp, pushout.inl_desc] using h'
      · intro b h
        rw [compApp, pushout.inl_desc]
      · intro b h
        have h' : a = b := by
          simpa only [coyoneda_map_src_app, compApp, pushout.inl_desc,
            Category.id_comp] using h
        simpa only [compApp, pushout.inl_desc] using h'
    · intro T T' f a b h h'
      simp only [compApp, pushout.inl_desc]

/-- The object of objects of the discrete representable groupoid is `U`. -/
theorem discrete_U (U : C) : (discrete U).U = U :=
  rfl

/-- The object of arrows of the discrete representable groupoid is `U`. -/
theorem discrete_R (U : C) : (discrete U).R = U :=
  rfl

/-- The source of the discrete representable groupoid is the identity. -/
theorem discrete_s (U : C) : (discrete U).s = 𝟙 U :=
  rfl

/-- The target of the discrete representable groupoid is the identity. -/
theorem discrete_t (U : C) : (discrete U).t = 𝟙 U :=
  rfl

/-- The composition of the discrete representable groupoid is the first pushout inclusion. -/
theorem discrete_c (U : C) : (discrete U).c = pushout.inl (𝟙 U) (𝟙 U) :=
  rfl

end Representable

/-- An explicit representable groupoid has a pushout of its source and target morphisms,
and its induced coyoneda quintuple satisfies the pointwise groupoid laws. -/
theorem Representable.spec {C : Type u} [Category.{v} C] (G : Representable C) :
    HasPushout G.s G.t ∧
      IsGroupoidInFunctors (coyoneda.obj (op G.U)) (coyoneda.obj (op G.R))
        (coyoneda.map G.s.op) (coyoneda.map G.t.op)
        (Representable.compApp G.s G.t G.c) :=
  ⟨inferInstance, G.isGroupoid⟩

end CategoryTheory.GroupoidInFunctors

end
