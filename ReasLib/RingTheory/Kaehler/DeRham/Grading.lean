/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.HomogeneousMap
public import ReasLib.RingTheory.Kaehler.DeRham
public import ReasLib.RingTheory.Kaehler.DeRham.Wedge
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The grading on the de Rham complex of a graded ring

This file defines the homogeneous pieces of Kähler differentials and higher relative forms for a
graded algebra. It also records compatibility with the de Rham differential and wedge product.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u v

namespace KaehlerDifferential.DeRham.Grading

variable {G : Type v} [DecidableEq G] [AddCommMonoid G]
variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : G → Submodule R A) [GradedAlgebra 𝒜]

/-- The degree-`g` submodule of `Ω[A⁄R]`, spanned by the forms `a₀ • D R A a₁` whose
coefficient and differentiated input are homogeneous of degrees summing to `g`. -/
def onePiece (g : G) : Submodule R Ω[A⁄R] :=
  Submodule.span R {ω | ∃ (g₀ g₁ : G) (a₀ a₁ : A),
    a₀ ∈ 𝒜 g₀ ∧ a₁ ∈ 𝒜 g₁ ∧ g₀ + g₁ = g ∧
      ω = a₀ • KaehlerDifferential.D R A a₁}

/-- A homogeneous basic one-form belongs to the piece indexed by the sum of its two degrees. -/
theorem oneBasic_mem {g₀ g₁ g : G} {a₀ a₁ : A}
    (ha₀ : a₀ ∈ 𝒜 g₀) (ha₁ : a₁ ∈ 𝒜 g₁) (hdeg : g₀ + g₁ = g) :
    a₀ • KaehlerDifferential.D R A a₁ ∈ onePiece R A 𝒜 g := sorry

/-- The degree-`g` submodule of relative `p`-forms, spanned by homogeneous basic forms whose
coefficient degree plus the degrees of their differential inputs is `g`. -/
def piece (p : ℕ) (g : G) : Submodule R (term R A p) :=
  Submodule.span R {ω | ∃ (g₀ : G) (gs : Fin p → G) (a₀ : A) (a : Fin p → A),
    a₀ ∈ 𝒜 g₀ ∧ (∀ i, a i ∈ 𝒜 (gs i)) ∧
      g₀ + ∑ i, gs i = g ∧ ω = basic R A p a₀ a}

/-- A homogeneous basic `p`-form belongs to the piece indexed by its total input degree. -/
theorem basic_mem {p : ℕ} {g₀ g : G} {gs : Fin p → G} {a₀ : A} {a : Fin p → A}
    (ha₀ : a₀ ∈ 𝒜 g₀) (ha : ∀ i, a i ∈ 𝒜 (gs i))
    (hdeg : g₀ + ∑ i, gs i = g) :
    basic R A p a₀ a ∈ piece R A 𝒜 p g := sorry

/-- The underlying function of the canonical comparison from presented one-forms to Kähler
differentials. -/
def toOneFormFun (x : term R A 1) : Ω[A⁄R] :=
  toExterior R A 1 x

/-- Additivity of the canonical comparison from presented one-forms to Kähler differentials. -/
theorem toOneForm_add (x y : term R A 1) :
    toOneFormFun R A (x + y) = toOneFormFun R A x + toOneFormFun R A y := sorry

/-- `R`-linearity of the canonical comparison from presented one-forms to Kähler differentials. -/
theorem toOneForm_smul (r : R) (x : term R A 1) :
    toOneFormFun R A (r • x) = r • toOneFormFun R A x := sorry

/-- The canonical `R`-linear comparison from presented one-forms to Kähler differentials. -/
def toOneForm : term R A 1 →ₗ[R] Ω[A⁄R] where
  toFun := toOneFormFun R A
  map_add' := toOneForm_add R A
  map_smul' := toOneForm_smul R A

/-- The direct Kähler-differential grading agrees with the degree-one presented-form grading under
the canonical comparison map. -/
theorem onePiece_eq_map_piece_one (g : G) :
    onePiece R A 𝒜 g = (piece R A 𝒜 1 g).map (toOneForm R A) := sorry

/-- The homogeneous pieces of `Ω[A⁄R]` form an internal direct sum. -/
theorem onePiece_isInternal : DirectSum.IsInternal (onePiece R A 𝒜) := sorry

/-- For every `p`, the homogeneous pieces of relative `p`-forms form an internal direct sum. -/
theorem piece_isInternal (p : ℕ) : DirectSum.IsInternal (piece R A 𝒜 p) := sorry

/-- The graded algebra action on relative `p`-forms respects the homogeneous pieces. -/
instance instGradedSMulPiece (p : ℕ) : SetLike.GradedSMul 𝒜 (piece R A 𝒜 p) := sorry

/-- The de Rham differential sends a homogeneous form to the piece of the same grading degree. -/
theorem d_mem {p : ℕ} {g : G} {x : term R A p} (hx : x ∈ piece R A 𝒜 p g) :
    d R A p x ∈ piece R A 𝒜 (p + 1) g := sorry

/-- The de Rham differential bundled as a linear map preserving the grading degree. -/
def dHom (p : ℕ) :
    GradedModule.MapsTo R (piece R A 𝒜 p) (piece R A 𝒜 (p + 1)) (fun g ↦ g) :=
  ⟨(d R A p).hom, fun _ _ hx ↦ d_mem R A 𝒜 hx⟩

/-- The underlying linear map of `dHom` is the canonical de Rham differential. -/
theorem dHom_toLinearMap (p : ℕ) :
    GradedModule.MapsTo.toLinearMap (dHom R A 𝒜 p) = (d R A p).hom := sorry

/-- Wedge multiplication adds the grading degrees of two homogeneous forms. -/
theorem wedge_mem {p q : ℕ} {g h : G} {x : term R A p} {y : term R A q}
    (hx : x ∈ piece R A 𝒜 p g) (hy : y ∈ piece R A 𝒜 q h) :
    formWedgeBilinear R A p q x y ∈ piece R A 𝒜 (p + q) (g + h) := sorry

end KaehlerDifferential.DeRham.Grading
