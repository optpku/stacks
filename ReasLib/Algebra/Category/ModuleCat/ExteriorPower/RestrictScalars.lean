/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.DegreeOne
public import ReasLib.LinearAlgebra.ExteriorPower.RestrictScalars

/-!
# Exterior powers and restriction of scalars

This file bundles the map on exterior powers induced by a morphism whose target is a module over
a different commutative ring.  The scalar restriction remains visible in the target object, so
the construction composes with `ModuleCat.restrictScalars` without changing ambient instances.

@stack 0H1C
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace ModuleCat.exteriorPower

variable {R S T : Type u}
variable [CommRing R] [CommRing S] [CommRing T]

/-- The map on degree-`n` exterior powers induced by a morphism into a restriction of scalars. -/
@[stacks 0H1C "exterior power of a scalar-restriction morphism"]
noncomputable def mapRestrictScalars (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (n : ℕ) :
    M.exteriorPower n ⟶ (ModuleCat.restrictScalars φ).obj (N.exteriorPower n) := by
  -- Local instance justification (noncanonical choice): φ specifies the scalar action and can differ from an ambient algebra map.
  letI : Algebra R S := φ.toAlgebra
  exact ConcreteCategory.ofHom
    (C := ModuleCat R)
    (_root_.exteriorPower.RestrictScalars.map (R := R) (S := S) n
      (show M →ₗ[R] _root_.RestrictScalars R S N from f.hom))

/-- `mapRestrictScalars` sends an exterior generator to the generator of its entrywise image. -/
@[simp, stacks 0H1C "exterior scalar restriction on generators"]
theorem mapRestrictScalars_mk (φ : R →+* S)
    {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) (n : ℕ) (m : Fin n → M) :
    mapRestrictScalars φ f n (mk m) =
      ModuleCat.exteriorPower.mk (R := S) (M := N) (fun i ↦ f (m i)) := sorry

/-- Exterior powers carry the identity scalar-restriction morphism to the corresponding identity
scalar-restriction morphism. -/
theorem mapRestrictScalars_id (φ : R →+* R) (hφ : φ = RingHom.id R)
    (M : ModuleCat.{v} R) (n : ℕ) :
    mapRestrictScalars φ (ModuleCat.restrictScalarsId'App φ hφ M).inv n =
      (ModuleCat.restrictScalarsId'App φ hφ (M.exteriorPower n)).inv := sorry

/-- Exterior powers preserve composition of morphisms over composable scalar maps, including the
canonical comparison between iterated and composite scalar restriction. -/
theorem mapRestrictScalars_comp (φ : R →+* S) (ψ : S →+* T) (χ : R →+* T)
    (hχ : χ = ψ.comp φ) {M : ModuleCat.{v} R} {N : ModuleCat.{v} S}
    {P : ModuleCat.{v} T}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N)
    (g : N ⟶ (ModuleCat.restrictScalars ψ).obj P) (n : ℕ) :
    mapRestrictScalars χ
        (f ≫ (ModuleCat.restrictScalars φ).map g ≫
          (ModuleCat.restrictScalarsComp' φ ψ χ hχ).inv.app P) n =
      mapRestrictScalars φ f n ≫
        (ModuleCat.restrictScalars φ).map (mapRestrictScalars ψ g n) ≫
        (ModuleCat.restrictScalarsComp' φ ψ χ hχ).inv.app (P.exteriorPower n) := sorry

/-- The first-exterior-power isomorphism commutes with maps into a scalar restriction. -/
theorem degreeOne_mapRestrictScalars (φ : R →+* S)
    {M : ModuleCat.{max u v} R} {N : ModuleCat.{max u v} S}
    (f : M ⟶ (ModuleCat.restrictScalars φ).obj N) :
    f ≫ (ModuleCat.restrictScalars φ).map (degreeOne N) =
      degreeOne M ≫ mapRestrictScalars φ f 1 := sorry

end ModuleCat.exteriorPower
