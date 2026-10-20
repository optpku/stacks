/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Uniqueness of Morphisms of Distinguished Triangles

This leaf packages the Hom-vanishing criteria which determine the middle
component of a morphism of distinguished triangles. Mathlib supplies the
underlying exactness and `Triangle.hom_ext`; the statements here combine those
primitive facts into the downstream-facing uniqueness API.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Pretriangulated.TriangleMorphism

open CategoryTheory.Limits

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {T T' : Triangle D} {φ ψ : T ⟶ T'}

/-- Stacks 0FWZ, Lemma 13.4.8 (1): if `Hom(T.obj₂, T'.obj₁)` is subsingleton, equality of third
components of parallel triangle morphisms determines their middle components. -/
@[stacks 0FWZ]
theorem hom₂_eq_of_subsingleton_hom_obj₂_obj₁
    (hT' : T' ∈ distTriang D) (h₃ : φ.hom₃ = ψ.hom₃)
    (h21 : Subsingleton (T.obj₂ ⟶ T'.obj₁)) :
    φ.hom₂ = ψ.hom₂ := sorry

/-- Stacks 0FWZ, Lemma 13.4.8 (2): if `Hom(T.obj₃, T'.obj₂)` is subsingleton, equality of first
components of parallel triangle morphisms determines their middle components. -/
@[stacks 0FWZ]
theorem hom₂_eq_of_subsingleton_hom_obj₃_obj₂
    (hT : T ∈ distTriang D) (h₁ : φ.hom₁ = ψ.hom₁)
    (h32 : Subsingleton (T.obj₃ ⟶ T'.obj₂)) :
    φ.hom₂ = ψ.hom₂ := sorry

/-- Stacks 0FWZ, Lemma 13.4.8 (3): if `Hom(T.obj₁, T'.obj₁)` and `Hom(T.obj₃, T'.obj₁)` are
subsingleton, equality of the third components determines the middle components of parallel
triangle morphisms. -/
@[stacks 0FWZ]
theorem hom₂_eq_of_subsingleton_hom_obj₁_obj₁_and_obj₃_obj₁
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₃ : φ.hom₃ = ψ.hom₃)
    (h11 : Subsingleton (T.obj₁ ⟶ T'.obj₁)) (h31 : Subsingleton (T.obj₃ ⟶ T'.obj₁)) :
    φ.hom₂ = ψ.hom₂ := sorry

/-- Stacks 0FWZ, Lemma 13.4.8 (4): if `Hom(T.obj₃, T'.obj₁)` and `Hom(T.obj₃, T'.obj₃)` are
subsingleton, equality of the first components determines the middle components of parallel
triangle morphisms. -/
@[stacks 0FWZ]
theorem hom₂_eq_of_subsingleton_hom_obj₃_obj₁_and_obj₃_obj₃
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₁ : φ.hom₁ = ψ.hom₁)
    (h31 : Subsingleton (T.obj₃ ⟶ T'.obj₁)) (h33 : Subsingleton (T.obj₃ ⟶ T'.obj₃)) :
    φ.hom₂ = ψ.hom₂ := sorry

/-- Stacks 0FWZ, Lemma 13.4.8 (5): if `Hom(T.obj₁⟦1⟧, T'.obj₃)` and `Hom(T.obj₃, T'.obj₁)` are
subsingleton, equality of the outer components determines the middle components of parallel
triangle morphisms. -/
@[stacks 0FWZ]
theorem hom₂_eq_of_subsingleton_hom_shift_obj₁_obj₃_and_obj₃_obj₁
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₁ : φ.hom₁ = ψ.hom₁) (h₃ : φ.hom₃ = ψ.hom₃)
    (h13 : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃))
    (h31 : Subsingleton (T.obj₃ ⟶ T'.obj₁)) :
    φ.hom₂ = ψ.hom₂ := sorry

/-- Stacks 0FWZ: the middle component of a morphism between distinguished triangles is determined
by its outer components under any of the five standard Hom-vanishing alternatives. -/
@[stacks 0FWZ]
theorem hom₂_eq_of_hom_vanishing
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₁ : φ.hom₁ = ψ.hom₁) (h₃ : φ.hom₃ = ψ.hom₃)
    (hvan :
      Subsingleton (T.obj₂ ⟶ T'.obj₁) ∨
        Subsingleton (T.obj₃ ⟶ T'.obj₂) ∨
          (Subsingleton (T.obj₁ ⟶ T'.obj₁) ∧ Subsingleton (T.obj₃ ⟶ T'.obj₁)) ∨
            (Subsingleton (T.obj₃ ⟶ T'.obj₁) ∧ Subsingleton (T.obj₃ ⟶ T'.obj₃)) ∨
              (Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃) ∧
                Subsingleton (T.obj₃ ⟶ T'.obj₁))) :
    φ.hom₂ = ψ.hom₂ := sorry

/-- Stacks 0FWZ: under the standard Hom-vanishing alternatives, a morphism between distinguished
triangles is determined by its first and third components. -/
@[stacks 0FWZ]
theorem ext_of_outer_eq_of_hom_vanishing
    (hT : T ∈ distTriang D) (hT' : T' ∈ distTriang D)
    (h₁ : φ.hom₁ = ψ.hom₁) (h₃ : φ.hom₃ = ψ.hom₃)
    (hvan :
      Subsingleton (T.obj₂ ⟶ T'.obj₁) ∨
        Subsingleton (T.obj₃ ⟶ T'.obj₂) ∨
          (Subsingleton (T.obj₁ ⟶ T'.obj₁) ∧ Subsingleton (T.obj₃ ⟶ T'.obj₁)) ∨
            (Subsingleton (T.obj₃ ⟶ T'.obj₁) ∧ Subsingleton (T.obj₃ ⟶ T'.obj₃)) ∨
              (Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ T'.obj₃) ∧
                Subsingleton (T.obj₃ ⟶ T'.obj₁))) :
    φ = ψ := sorry

end CategoryTheory.Pretriangulated.TriangleMorphism
