/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Base change of integral and finite morphisms of algebraic spaces

Integral and finite morphisms of algebraic spaces are preserved by arbitrary
pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
  CategoryTheory.MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Representable presheaves are algebraic spaces, so testing the universal
-- property on them shows that the underlying presheaf square is a pullback.
private theorem isPullback_functorOfPoints {S : Scheme.{u}}
    {P X Y B : AlgebraicSpace S} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ B} {g : Y ⟶ B} (sq : IsPullback fst snd f g) :
    IsPullback (C := (Over S)ᵒᵖ ⥤ Type u) fst snd f g := by
  apply IsPullback.of_forall_isPullback_app
  intro T
  rw [Types.isPullback_iff]
  refine ⟨congrArg (fun k : P ⟶ B ↦ k.app T) sq.w, ?_, ?_⟩
  · intro x y ⟨hx, hy⟩
    apply yonedaEquiv.symm.injective
    apply sq.hom_ext (W := ofOver T.unop)
    · apply yonedaEquiv.injective
      change fst.app T (yonedaEquiv (yonedaEquiv.symm x)) =
        fst.app T (yonedaEquiv (yonedaEquiv.symm y))
      simpa only [Equiv.apply_symm_apply] using hx
    · apply yonedaEquiv.injective
      change snd.app T (yonedaEquiv (yonedaEquiv.symm x)) =
        snd.app T (yonedaEquiv (yonedaEquiv.symm y))
      simpa only [Equiv.apply_symm_apply] using hy
  · intro x y hxy
    have w : (yonedaEquiv.symm x : ofOver T.unop ⟶ X) ≫ f =
        (yonedaEquiv.symm y : ofOver T.unop ⟶ Y) ≫ g := by
      simpa only [yonedaEquiv_symm_naturality_right] using
        congrArg yonedaEquiv.symm hxy
    obtain ⟨l, hl₁, hl₂⟩ := sq.exists_lift (W := ofOver T.unop)
      (yonedaEquiv.symm x) (yonedaEquiv.symm y) w
    refine ⟨yonedaEquiv l, ?_, ?_⟩
    · have h := congrArg (fun k : ofOver T.unop ⟶ X ↦ yonedaEquiv k) hl₁
      change fst.app T (yonedaEquiv l) = yonedaEquiv (yonedaEquiv.symm x) at h
      simpa only [Equiv.apply_symm_apply] using h
    · have h := congrArg (fun k : ofOver T.unop ⟶ Y ↦ yonedaEquiv k) hl₂
      change snd.app T (yonedaEquiv l) = yonedaEquiv (yonedaEquiv.symm y) at h
      simpa only [Equiv.apply_symm_apply] using h

/-- An integral morphism remains integral in any pullback square. -/
theorem isIntegralHom_of_isPullback {S : Scheme.{u}}
    {X Y Y' B : AlgebraicSpace S} {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y}
    {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) (hg : IsIntegralHom g) :
    IsIntegralHom g' := by
  constructor
  intro Z _ a
  obtain ⟨W, snd, fst, h, hW, hsnd⟩ := hg.affine_integral (a ≫ f)
  have sq' := isPullback_functorOfPoints sq
  obtain ⟨k, hk₁, hk₂⟩ := sq'.exists_lift fst (yoneda.map snd ≫ a)
    (by simpa only [Category.assoc] using h.w)
  refine ⟨W, snd, k, ?_, hW, hsnd⟩
  exact IsPullback.of_right (by simpa only [hk₁] using h) hk₂ sq'

namespace IsIntegralHom

/-- The second projection from a pullback of an integral morphism is integral. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsIntegralHom f) (g : Z ⟶ Y) [HasPullback f g] :
    IsIntegralHom (pullback.snd f g) :=
  isIntegralHom_of_isPullback (IsPullback.of_hasPullback f g) hf

end IsIntegralHom

/-- The second projection from a pullback of an integral morphism is integral
when the source morphism is available as an instance. -/
instance isIntegralHom_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsIntegralHom f] [HasPullback f g] :
    IsIntegralHom (pullback.snd f g) :=
  IsIntegralHom.pullback_snd inferInstance g

/-- Integral morphisms are stable under arbitrary base change. -/
instance isIntegralHom_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsIntegralHom S : MorphismProperty (AlgebraicSpace S)) :=
  ⟨isIntegralHom_of_isPullback⟩

/-- A finite morphism remains finite in any pullback square. -/
theorem isFinite_of_isPullback {S : Scheme.{u}}
    {X Y Y' B : AlgebraicSpace S} {f : X ⟶ B} {g : Y ⟶ B} {f' : Y' ⟶ Y}
    {g' : Y' ⟶ X} (sq : IsPullback f' g' g f) (hg : IsFinite g) : IsFinite g' := by
  constructor
  intro Z _ a
  obtain ⟨W, snd, fst, h, hW, hsnd⟩ := hg.affine_finite (a ≫ f)
  have sq' := isPullback_functorOfPoints sq
  obtain ⟨k, hk₁, hk₂⟩ := sq'.exists_lift fst (yoneda.map snd ≫ a)
    (by simpa only [Category.assoc] using h.w)
  refine ⟨W, snd, k, ?_, hW, hsnd⟩
  exact IsPullback.of_right (by simpa only [hk₁] using h) hk₂ sq'

namespace IsFinite

/-- The second projection from a pullback of a finite morphism is finite. -/
theorem pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : IsFinite f) (g : Z ⟶ Y) [HasPullback f g] :
    IsFinite (pullback.snd f g) :=
  isFinite_of_isPullback (IsPullback.of_hasPullback f g) hf

end IsFinite

/-- The second projection from a pullback of a finite morphism is finite when
the source morphism is available as an instance. -/
instance isFinite_pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [IsFinite f] [HasPullback f g] :
    IsFinite (pullback.snd f g) :=
  IsFinite.pullback_snd inferInstance g

/-- Finite morphisms are stable under arbitrary base change. -/
instance isFinite_isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@IsFinite S : MorphismProperty (AlgebraicSpace S)) :=
  ⟨isFinite_of_isPullback⟩

end AlgebraicGeometry.AlgebraicSpace
