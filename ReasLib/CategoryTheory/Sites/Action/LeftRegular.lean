/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Action.Concrete

/-!
# Left-regular actions

This module owns the elementary left-regular action constructions used by action sites.  It is
independent of Grothendieck topologies and points, so both site and topos APIs can depend on it
without introducing an upward dependency.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace Action

noncomputable section

variable (G : Type u) [Monoid G]

/-- The orbit of a point in a `G`-action, parametrized by the left-regular `G`-action. -/
def leftRegularOrbit {X : Action (Type u) G} (x : X.V) : G → X.V :=
  fun g ↦ X.ρ g x

/-- The left-regular orbit through a point is equivariant. -/
theorem leftRegularOrbit_equivariant {X : Action (Type u) G} (x : X.V) :
    ∀ h : G,
      (Action.leftRegular G).ρ h ≫
        (↾fun g : G ↦ leftRegularOrbit G x g) =
      (↾fun g : G ↦ leftRegularOrbit G x g) ≫ X.ρ h := sorry

/-- The equivariant orbit map from the left-regular `G`-set through a chosen point. -/
def leftRegularOrbitHom {X : Action (Type u) G} (x : X.V) :
    Action.leftRegular G ⟶ X where
  hom := ↾fun g : G ↦ leftRegularOrbit G x g
  comm := leftRegularOrbit_equivariant G x

/-- An equivariant map out of the left-regular `G`-set is determined by its value at `1`. -/
theorem leftRegularOrbitHom_eq_of_apply_one
    {X : Action (Type u) G} (f : Action.leftRegular G ⟶ X) (x : X.V)
    (hf : f.hom (1 : G) = x) :
    f = leftRegularOrbitHom G x := sorry

/-- Equivariant maps transport left-regular orbit maps. -/
theorem leftRegularOrbitHom_comp
    {X Y : Action (Type u) G} (f : X ⟶ Y) (x : X.V) :
    leftRegularOrbitHom G (f.hom x) = leftRegularOrbitHom G x ≫ f := sorry

/-- Orbit maps with equal images after equivariant maps have equal composites. -/
theorem leftRegularOrbitHom_comp_eq
    {Y₁ Y₂ X : Action (Type u) G} {f₁ : Y₁ ⟶ X} {f₂ : Y₂ ⟶ X}
    (y₁ : Y₁.V) (y₂ : Y₂.V) (h : f₁.hom y₁ = f₂.hom y₂) :
    leftRegularOrbitHom G y₁ ≫ f₁ = leftRegularOrbitHom G y₂ ≫ f₂ := sorry

/-- Right multiplication by `g` commutes with the left-regular action. -/
theorem leftRegularRightMul_comm (g : G) :
    ∀ h : G,
      (Action.leftRegular G).ρ h ≫
        (↾fun x : G ↦ x * g) =
      (↾fun x : G ↦ x * g) ≫ (Action.leftRegular G).ρ h := sorry

/-- The endomorphism of the left-regular `G`-set given by right multiplication by `g`. -/
def leftRegularRightMul (g : G) : Action.leftRegular G ⟶ Action.leftRegular G where
  hom := ↾fun x : G ↦ x * g
  comm := leftRegularRightMul_comm G g

/-- Right multiplication by `1` is the identity of the left-regular `G`-set. -/
@[simp]
theorem leftRegularRightMul_one :
    leftRegularRightMul G 1 = 𝟙 (Action.leftRegular G) := sorry

/-- Right multiplications compose according to multiplication in `G`. -/
@[simp]
theorem leftRegularRightMul_mul (g h : G) :
    leftRegularRightMul G (g * h) =
      leftRegularRightMul G g ≫ leftRegularRightMul G h := sorry

/-- Precomposing an orbit map by right multiplication translates its chosen point. -/
theorem leftRegularRightMul_comp_orbit
    {X : Action (Type u) G} (x : X.V) (g : G) :
    leftRegularRightMul G g ≫ leftRegularOrbitHom G x =
      leftRegularOrbitHom G (X.ρ g x) := sorry

/-- The orbit map in the left-regular action is right multiplication. -/
theorem leftRegularOrbitHom_leftRegular (g : (Action.leftRegular G).V) :
    leftRegularOrbitHom G g = leftRegularRightMul G g := sorry

/-- The raw right-translation operation on functions `G → S`. -/
def rightTranslation (S : Type v) (g : G) (psi : G → S) : G → S :=
  fun x ↦ psi (x * g)

/-- Right translation by `1` is the identity on functions. -/
theorem rightTranslation_one (S : Type v) (psi : G → S) :
    rightTranslation G S 1 psi = psi := sorry

/-- Right translations define a left `G`-action on functions. -/
theorem rightTranslation_mul (S : Type v) (g h : G) (psi : G → S) :
    rightTranslation G S (g * h) psi =
      rightTranslation G S g (rightTranslation G S h psi) := sorry

/-- The named right-translation `G`-action on functions `G → S`.

This is a definition rather than a global instance: the same function type may carry other
natural actions in downstream developments. -/
@[reducible]
def rightTranslationMulAction (S : Type v) : MulAction G (G → S) where
  smul := rightTranslation G S
  one_smul := rightTranslation_one G S
  mul_smul := rightTranslation_mul G S

/-- The `G`-set of functions `G → S` equipped with the named right-translation action. -/
def rightTranslationAction (S : Type v) : Action (Type (max u v)) G :=
  @Action.ofMulAction G (G → S) _ (rightTranslationMulAction G S)

/-- In the named right-translation `G`-set, `g` acts by precomposition with `x ↦ x * g`. -/
@[simp]
theorem rightTranslationAction_rho_apply (S : Type v) (g x : G) (psi : G → S) :
    (rightTranslationAction G S).ρ g psi x = psi (x * g) := sorry

end

end Action
