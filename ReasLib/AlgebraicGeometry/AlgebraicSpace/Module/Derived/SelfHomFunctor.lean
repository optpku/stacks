/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.HomFunctor

/-!
# Self-Hom functor of derived pullbacks

Derived endomorphisms form a presheaf on algebraic spaces over the base.
For a relatively perfect complex with vanishing negative fibre self-Ext on a
proper, flat, finitely presented morphism, this presheaf is represented by an
affine algebraic space of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open scoped DerivedExt

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Restriction of a derived self-Hom after base change along a morphism of
algebraic spaces over `Y`. -/
def selfHomRestrict (f : X ⟶ Y) (E : ModuleDerived X) {σ τ : Over Y} (h : τ ⟶ σ)
    (u : baseChangePullback f σ.hom E ⟶ baseChangePullback f σ.hom E) :
    baseChangePullback f τ.hom E ⟶ baseChangePullback f τ.hom E :=
  baseChangeHom f E E h.left (Over.w h) u

/-- Derived self-Hom restriction preserves identity morphisms over the base. -/
theorem selfHomRestrict_id (f : X ⟶ Y) (E : ModuleDerived X) (σ : Over Y) :
    TypeCat.ofHom (selfHomRestrict f E (𝟙 σ)) = 𝟙 _ := sorry

/-- Derived self-Hom restriction reverses composition over the base. -/
theorem selfHomRestrict_comp (f : X ⟶ Y) (E : ModuleDerived X)
    {σ τ υ : Over Y} (h : τ ⟶ σ) (g : υ ⟶ τ) :
    TypeCat.ofHom (selfHomRestrict f E (g ≫ h)) =
      TypeCat.ofHom (selfHomRestrict f E h) ≫
        TypeCat.ofHom (selfHomRestrict f E g) := sorry

/-- The functor `V ↦ Hom_{𝒪_{X_V}}(E_V, E_V)` on algebraic spaces over `Y`. -/
def selfHomFunctorOver (f : X ⟶ Y) (E : ModuleDerived X) :
    (Over Y)ᵒᵖ ⥤ Type (u + 1) where
  obj σ :=
    baseChangePullback f σ.unop.hom E ⟶ baseChangePullback f σ.unop.hom E
  map h := TypeCat.ofHom (selfHomRestrict f E h.unop)
  map_id σ := selfHomRestrict_id f E σ.unop
  map_comp h g := selfHomRestrict_comp f E h.unop g.unop

/-- Evaluating `selfHomFunctorOver` at an algebraic space over `Y` yields derived
self-Hom of the base-changed complex. -/
theorem selfHomFunctorOver_obj (f : X ⟶ Y) (E : ModuleDerived X) (σ : Over Y) :
    (selfHomFunctorOver f E).obj (op σ) =
      (baseChangePullback f σ.hom E ⟶ baseChangePullback f σ.hom E) := sorry

/-- `selfHomFunctorOver` acts on morphisms of algebraic spaces over `Y` by
`selfHomRestrict`. -/
theorem selfHomFunctorOver_map (f : X ⟶ Y) (E : ModuleDerived X)
    {σ τ : Over Y} (h : τ ⟶ σ) :
    (selfHomFunctorOver f E).map h.op = TypeCat.ofHom (selfHomRestrict f E h) := sorry

/-- The restriction of `selfHomFunctorOver` to schemes over `Y`. -/
def selfHomFunctor (f : X ⟶ Y) (E : ModuleDerived X) :
    (SchemeOver Y)ᵒᵖ ⥤ Type (u + 1) :=
  SchemeOver.toOver.op ⋙ selfHomFunctorOver f E

/-- Evaluating `selfHomFunctor` at a scheme over `Y` yields derived self-Hom of
the base-changed complex. -/
theorem selfHomFunctor_obj (f : X ⟶ Y) (E : ModuleDerived X) (σ : SchemeOver Y) :
    (selfHomFunctor f E).obj (op σ) =
      (baseChangePullback f σ.hom E ⟶ baseChangePullback f σ.hom E) := sorry

variable (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
variable (E : ModuleDerived X)

/-- All negative self-Ext groups of a relatively perfect complex with vanishing
negative fibre self-Ext vanish after arbitrary base change. -/
theorem negativeSelfExt_eq_zero
    (hE : IsPerfectRelativeTo f E)
    (h_vanish : ∀ y : FieldValuedPoint Y, fiberNegativeExtVanish f E E y)
    {V : AlgebraicSpace S} (g : V ⟶ Y) (i : ℤ) (hi : i < 0) :
    Subsingleton (Ext⁽i⁾(baseChangePullback f g E, baseChangePullback f g E)) := sorry

/-- Negative self-Ext vanishing on every field-valued fibre of a relatively
perfect complex persists on fibres over any new base. -/
theorem fiberNegativeSelfExtVanish_baseChange
    (hE : IsPerfectRelativeTo f E)
    (h_vanish : ∀ y : FieldValuedPoint Y, fiberNegativeExtVanish f E E y)
    {V : AlgebraicSpace S} (g : V ⟶ Y) (v : FieldValuedPoint V) :
    fiberNegativeExtVanish (Limits.pullback.snd f g)
      (baseChangePullback f g E) (baseChangePullback f g E) v := sorry

/-- The derived self-Hom presheaf of a relatively perfect complex with vanishing
negative fibre self-Ext is represented by an affine, finitely presented
algebraic space over the base. -/
theorem selfHomFunctorOver_isAffineFinitePresentation
    (hE : IsPerfectRelativeTo f E)
    (h_vanish : ∀ y : FieldValuedPoint Y, fiberNegativeExtVanish f E E y) :
    ∃ (F : AlgebraicSpace S) (π : F ⟶ Y),
      Affine π ∧ FinitePresentation π ∧
        Nonempty (selfHomFunctorOver f E ≅ yoneda.obj (Over.mk π)) := sorry

/-- The scheme-restricted derived self-Hom presheaf of a relatively perfect
complex with vanishing negative fibre self-Ext is represented by an affine,
finitely presented algebraic space over the base. -/
theorem selfHomFunctor_isAffineFinitePresentation
    (hE : IsPerfectRelativeTo f E)
    (h_vanish : ∀ y : FieldValuedPoint Y, fiberNegativeExtVanish f E E y) :
    IsAffineFinitePresentationOver (selfHomFunctor f E) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
