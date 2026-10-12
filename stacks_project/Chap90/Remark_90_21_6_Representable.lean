/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap90.Remark_90_21_6_GroupoidInFunctors

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
  sorry

/-- The coyoneda interpretation of object-level target is precomposition with `t`. -/
theorem coyoneda_map_tgt_app {U R : C} (t : U ⟶ R) {T : C} (a : R ⟶ T) :
    (coyoneda.map t.op).app T a = t ≫ a :=
  sorry

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
  sorry

/-- The target of a composite `T`-point is the target of the later arrow.
This is the groupoid target law, available only when the coyoneda quintuple is a
groupoid in functors; equivalently `t ≫ c = t ≫ pushout.inl s t`. -/
theorem compApp_tgt {U R : C} (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    [h_groupoid : isCoyonedaGroupoid s t c] {T : C} (a b : R ⟶ T)
    (h : s ≫ a = t ≫ b) :
    t ≫ compApp s t c a b h = t ≫ a :=
  sorry

/-- Object-level source law of composition: postcomposing `c` with `s` recovers the
earlier-arrow inclusion of the pushout. -/
theorem source_comp {U R : C} (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    [h_groupoid : isCoyonedaGroupoid s t c] :
    s ≫ c = s ≫ pushout.inr s t :=
  sorry

/-- Object-level target law of composition: postcomposing `c` with `t` recovers the
later-arrow inclusion of the pushout. -/
theorem target_comp {U R : C} (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    [h_groupoid : isCoyonedaGroupoid s t c] :
    t ≫ c = t ≫ pushout.inl s t :=
  sorry

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

/-- Projection of the bundled pushout existence field. -/
instance instHasPushout (G : Representable C) : HasPushout G.s G.t :=
  G.hasPushout

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
  sorry

/-- The object representing arrows in a packaged representable groupoid is the supplied `R`. -/
theorem of_R (U R : C) (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    (h : isCoyonedaGroupoid s t c) : (of U R s t c h).R = R :=
  sorry

/-- The source morphism of a packaged representable groupoid is the supplied `s`. -/
theorem of_s (U R : C) (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    (h : isCoyonedaGroupoid s t c) : (of U R s t c h).s = s :=
  sorry

/-- The target morphism of a packaged representable groupoid is the supplied `t`. -/
theorem of_t (U R : C) (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    (h : isCoyonedaGroupoid s t c) : (of U R s t c h).t = t :=
  sorry

/-- The composition morphism of a packaged representable groupoid is the supplied `c`. -/
theorem of_c (U R : C) (s t : U ⟶ R) [HasPushout s t] (c : R ⟶ pushout s t)
    (h : isCoyonedaGroupoid s t c) : (of U R s t c h).c = c :=
  sorry

/-- The coyoneda quintuple of a representable groupoid in functors is a groupoid in functors. -/
instance instIsGroupoidInFunctors (G : Representable C) :
    IsGroupoidInFunctors G.functorU G.functorR G.functorSrc G.functorTgt
      (compApp G.s G.t G.c) :=
  G.isGroupoid

/-- The identity-identity span with vertex `U` is a pushout cocone. -/
def pushoutCocone_id_id (U : C) : PushoutCocone (𝟙 U) (𝟙 U) :=
  PushoutCocone.mk (𝟙 U) (𝟙 U) rfl

/-- The identity-identity cocone on `U` is colimiting, with descendant the first inclusion. -/
def isColimit_id_id (U : C) : IsColimit (pushoutCocone_id_id U) where
  desc s := PushoutCocone.inl s
  fac := sorry
  uniq := sorry

/-- The pushout of two identity morphisms on `U` exists. -/
instance hasPushout_id_id {U : C} : HasPushout (𝟙 U) (𝟙 U) :=
  HasColimit.mk ⟨pushoutCocone_id_id U, isColimit_id_id U⟩

/-- The discrete representable groupoid in functors on an object `U`. -/
def discrete (U : C) : Representable C where
  U := U
  R := U
  s := 𝟙 U
  t := 𝟙 U
  c := pushout.inl (𝟙 U) (𝟙 U)
  isGroupoid := sorry

/-- The object of objects of the discrete representable groupoid is `U`. -/
theorem discrete_U (U : C) : (discrete U).U = U :=
  sorry

/-- The object of arrows of the discrete representable groupoid is `U`. -/
theorem discrete_R (U : C) : (discrete U).R = U :=
  sorry

/-- The source of the discrete representable groupoid is the identity. -/
theorem discrete_s (U : C) : (discrete U).s = 𝟙 U :=
  sorry

/-- The target of the discrete representable groupoid is the identity. -/
theorem discrete_t (U : C) : (discrete U).t = 𝟙 U :=
  sorry

/-- The composition of the discrete representable groupoid is the first pushout inclusion. -/
theorem discrete_c (U : C) : (discrete U).c = pushout.inl (𝟙 U) (𝟙 U) :=
  sorry

end Representable

end CategoryTheory.GroupoidInFunctors

end
