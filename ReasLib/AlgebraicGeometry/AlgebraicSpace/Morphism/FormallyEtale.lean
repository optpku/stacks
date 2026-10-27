/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting

/-!
# Formally étale morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is formally étale when it is
formally étale as a transformation of functors of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is formally étale if it is formally étale as
a transformation of functors of points. -/
class FormallyEtale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop where
  /-- The morphism is formally étale as a transformation of functors. -/
  ofFunctor : Scheme.Over.FormallyEtale f

/-- A morphism of algebraic spaces is formally étale if and only if it is
formally étale as a transformation of functors of points. -/
theorem formallyEtale_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyEtale f ↔ Scheme.Over.FormallyEtale f :=
  ⟨fun hf ↦ hf.ofFunctor, fun hf ↦ ⟨hf⟩⟩

namespace FormallyEtale

/-- A morphism of algebraic spaces that is formally étale as a transformation
of functors of points is formally étale. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Scheme.Over.FormallyEtale f) : FormallyEtale f :=
  ⟨hf⟩

/-- A formally étale morphism of algebraic spaces is formally étale as a
transformation of functors of points. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallyEtale f] : Scheme.Over.FormallyEtale f :=
  FormallyEtale.ofFunctor

set_option backward.isDefEq.respectTransparency false in
/-- Yoneda expresses the sectionwise definition as unique lifts from affine schemes. -/
private theorem iff_unique_lift_ofOver {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyEtale f ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left] (i : T ⟶ T')
        [IsFirstOrderThickening i.left] (a : ofOver T ⟶ X) (b : ofOver T' ⟶ Y),
        a ≫ f = (yoneda.map i : ofOver T ⟶ ofOver T') ≫ b →
          ∃! l : ofOver T' ⟶ X,
            (yoneda.map i : ofOver T ⟶ ofOver T') ≫ l = a ∧ l ≫ f = b := by
  have lift_iff {T T' : Over S} (i : T ⟶ T')
      (a : ofOver T ⟶ X) (b : ofOver T' ⟶ Y) (l : ofOver T' ⟶ X) :
      Scheme.Over.liftPair f i (yonedaEquiv l) = (yonedaEquiv a, yonedaEquiv b) ↔
        (yoneda.map i : ofOver T ⟶ ofOver T') ≫ l = a ∧ l ≫ f = b := by
    change (X.functorOfPoints.map i.op (yonedaEquiv l), f.app _ (yonedaEquiv l)) =
      (yonedaEquiv a, yonedaEquiv b) ↔ _
    rw [Prod.mk.injEq, yonedaEquiv_naturality, ← yonedaEquiv_comp]
    exact ⟨fun h ↦ ⟨yonedaEquiv.injective h.1, yonedaEquiv.injective h.2⟩,
      fun h ↦ ⟨congrArg yonedaEquiv h.1, congrArg yonedaEquiv h.2⟩⟩
  constructor
  · intro hf T T' _ _ i _ a b h
    have h' : f.app _ (yonedaEquiv a) = Y.functorOfPoints.map i.op (yonedaEquiv b) := by
      rw [← yonedaEquiv_comp, yonedaEquiv_naturality]
      exact congrArg yonedaEquiv h
    obtain ⟨x', hx', huniq⟩ := hf.ofFunctor.unique_lift i (yonedaEquiv a) (yonedaEquiv b) h'
    refine ⟨yonedaEquiv.symm x', ?_, ?_⟩
    · apply (lift_iff i a b _).mp
      simpa only [Equiv.apply_symm_apply] using hx'
    · intro l hl
      apply yonedaEquiv.injective
      simpa only [Equiv.apply_symm_apply] using
        huniq (yonedaEquiv l) ((lift_iff i a b l).mpr hl)
  · intro hf
    refine ⟨⟨?_⟩⟩
    intro T T' _ _ i _ x y h
    have h' : (yonedaEquiv.symm x : ofOver T ⟶ X) ≫ f =
        (yoneda.map i : ofOver T ⟶ ofOver T') ≫ yonedaEquiv.symm y := by
      change f.app _ x = Y.functorOfPoints.map i.op y at h
      rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_left, h]
    obtain ⟨l, hl, huniq⟩ := hf i (yonedaEquiv.symm x) (yonedaEquiv.symm y) h'
    refine ⟨yonedaEquiv l, ?_, ?_⟩
    · simpa only [Equiv.apply_symm_apply] using
        (lift_iff i (yonedaEquiv.symm x) (yonedaEquiv.symm y) l).mpr hl
    · intro x' hx'
      have hl' := (lift_iff i (yonedaEquiv.symm x) (yonedaEquiv.symm y)
        (yonedaEquiv.symm x')).mp (by simpa only [Equiv.apply_symm_apply] using hx')
      simpa only [Equiv.apply_symm_apply] using congrArg yonedaEquiv (huniq _ hl')

set_option backward.isDefEq.respectTransparency false in
/-- The identity morphism of an algebraic space is formally étale. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    FormallyEtale (𝟙 X) := by
  apply (iff_unique_lift_ofOver _).mpr
  intro T T' _ _ i _ a b h
  refine ⟨b, ⟨?_, by simp⟩, ?_⟩
  · simpa using h.symm
  · intro l hl
    simpa using hl.2

/-- A formally étale morphism of algebraic spaces yields a formally étale
transformation of functors of points. -/
instance toSchemeOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallyEtale f] : Scheme.Over.FormallyEtale f :=
  spec

/-- The composite of formally étale morphisms of algebraic spaces is formally
étale. -/
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FormallyEtale f] [FormallyEtale g] :
    FormallyEtale (f ≫ g) := by
  apply (iff_unique_lift_ofOver _).mpr
  intro T T' _ _ i _ a b h
  let j : ofOver T ⟶ ofOver T' := yoneda.map i
  obtain ⟨c, hc, hc_unique⟩ := (iff_unique_lift_ofOver g).mp inferInstance i (a ≫ f) b
    (by simpa only [Category.assoc] using h)
  obtain ⟨l, hl, hl_unique⟩ :=
    (iff_unique_lift_ofOver f).mp inferInstance i a c hc.1.symm
  refine ⟨l, ⟨hl.1, ?_⟩, ?_⟩
  · simpa only [← Category.assoc, hl.2] using hc.2
  · intro m hm
    apply hl_unique m
    refine ⟨hm.1, hc_unique (m ≫ f) ⟨?_, ?_⟩⟩
    · change j ≫ (m ≫ f) = a ≫ f
      have hj : j ≫ m = a := hm.1
      rw [← Category.assoc, hj]
    · simpa only [Category.assoc] using hm.2

/-- Formally étale morphisms of algebraic spaces are stable under composition. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FormallyEtale S : MorphismProperty (AlgebraicSpace S)) :=
  ⟨fun f g hf hg ↦ @comp _ _ _ _ f g hf hg⟩

/-- Formally étale morphisms of algebraic spaces are stable under
arbitrary base change. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FormallyEtale S : MorphismProperty (AlgebraicSpace S)) where
  of_isPullback {X Y Y' Z f g p q} sq hg := by
    apply (iff_unique_lift_ofOver _).mpr
    intro T T' _ _ i _ a b h
    let j : ofOver T ⟶ ofOver T' := yoneda.map i
    change a ≫ q = j ≫ b at h
    change ∃! l : ofOver T' ⟶ Y', j ≫ l = a ∧ l ≫ q = b
    have h' : (a ≫ p) ≫ g = j ≫ (b ≫ f) := by
      calc
        (a ≫ p) ≫ g = (a ≫ q) ≫ f := by rw [Category.assoc, sq.w, Category.assoc]
        _ = (j ≫ b) ≫ f := by rw [h]
        _ = j ≫ (b ≫ f) := Category.assoc _ _ _
    obtain ⟨c, hc, hc_unique⟩ := (iff_unique_lift_ofOver g).mp hg i (a ≫ p) (b ≫ f) h'
    change j ≫ c = a ≫ p ∧ c ≫ g = b ≫ f at hc
    change ∀ c' : ofOver T' ⟶ Y,
      j ≫ c' = a ≫ p ∧ c' ≫ g = b ≫ f → c' = c at hc_unique
    obtain ⟨l, hlp, hlq⟩ := sq.exists_lift c b hc.2
    refine ⟨l, ⟨?_, hlq⟩, ?_⟩
    · apply sq.hom_ext
      · simpa only [Category.assoc, hlp] using hc.1
      · simpa only [Category.assoc, hlq] using h.symm
    · intro m hm
      apply sq.hom_ext
      · have hmp : m ≫ p = c := hc_unique (m ≫ p) ⟨by
          simpa only [← Category.assoc, hm.1], by
          calc
            (m ≫ p) ≫ g = (m ≫ q) ≫ f := by rw [Category.assoc, sq.w, Category.assoc]
            _ = b ≫ f := by rw [hm.2]⟩
        exact hmp.trans hlp.symm
      · exact hm.2.trans hlq.symm

/-- The base-change projection `pullback.snd f g` of a formally étale
morphism `f : X ⟶ Y` is formally étale. -/
instance pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [FormallyEtale f] :
    FormallyEtale (pullback.snd f g) :=
  MorphismProperty.pullback_snd (P := @FormallyEtale S) f g inferInstance

end FormallyEtale

end AlgebraicGeometry.AlgebraicSpace
