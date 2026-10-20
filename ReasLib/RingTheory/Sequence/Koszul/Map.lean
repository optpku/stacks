/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of Koszul complexes

@stack 0GZJ

A linear map intertwining two linear forms induces a map of their Koszul complexes. The
degreewise exterior-power map is the computational owner; compatibility with the differentials
is a proof field of the bundled chain map.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace KoszulComplex

variable {R : Type u} [CommRing R]
variable {E : Type v} [AddCommGroup E] [Module R E]
variable {E' : Type v} [AddCommGroup E'] [Module R E']
variable {E'' : Type v} [AddCommGroup E''] [Module R E'']
variable {φ : E →ₗ[R] R} {φ' : E' →ₗ[R] R} {φ'' : E'' →ₗ[R] R}

/-- The degree-`n` exterior-power map underlying a map of Koszul complexes. -/
@[stacks 0GZJ "degreewise map of Koszul complexes"]
noncomputable def mapComponent (ψ : E →ₗ[R] E') (n : ℕ) :
    (ModuleCat.of R E).exteriorPower n ⟶ (ModuleCat.of R E').exteriorPower n :=
  ModuleCat.exteriorPower.map (ModuleCat.ofHom ψ) n

/-- A compatible linear map induces a map of Koszul complexes. -/
@[stacks 0GZJ "linear maps induce Koszul chain maps"]
noncomputable def map (ψ : E →ₗ[R] E') (hψ : φ'.comp ψ = φ) :
    koszulComplex φ ⟶ koszulComplex φ' where
  f n := mapComponent ψ n
  comm' := sorry

/-- The components of the induced Koszul map are the corresponding exterior-power maps. -/
@[simp]
theorem map_f (ψ : E →ₗ[R] E') (hψ : φ'.comp ψ = φ) (n : ℕ) :
    (map ψ hψ).f n = mapComponent ψ n := sorry

/-- The compatibility equation for a composite of maps of linear forms. -/
theorem comp_compatible (ψ : E →ₗ[R] E') (χ : E' →ₗ[R] E'')
    (hψ : φ'.comp ψ = φ) (hχ : φ''.comp χ = φ') :
    φ''.comp (χ.comp ψ) = φ := sorry

/-- The Koszul map induced by the identity linear map is the identity chain map. -/
@[simp]
theorem map_id (φ : E →ₗ[R] R) :
    map (φ := φ) (φ' := φ) LinearMap.id (LinearMap.comp_id φ) =
      𝟙 (koszulComplex φ) := sorry

/-- Koszul maps induced by compatible linear maps preserve composition. -/
theorem map_comp (ψ : E →ₗ[R] E') (χ : E' →ₗ[R] E'')
    (hψ : φ'.comp ψ = φ) (hχ : φ''.comp χ = φ') :
    map (χ.comp ψ) (comp_compatible ψ χ hψ hχ) =
      map ψ hψ ≫ map χ hχ := sorry

end KoszulComplex
