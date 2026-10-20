/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Derivation.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Residue

/-!
# Restriction of residue derivations along complete local algebra morphisms

Restriction by precomposition is a residue-field-linear map on derivations. Injectivity
of this restriction map implies surjectivity of the complete local algebra morphism.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CompleteLocalAlgCat
namespace Hom

/-- Restriction of residue derivations along a complete local algebra morphism is the
residue-field-linear map given by precomposition with its underlying algebra map. -/
def mapDerivation {R S : CompleteLocalAlgCat Λ k} (f : Hom R S) :
    Derivation Λ S.carrier k →ₗ[k] Derivation Λ R.carrier k where
  toFun D := by
    have leibniz (left right : R.carrier) :
        (D.toLinearMap.comp f.hom.toLinearMap) (left * right) =
          left • (D.toLinearMap.comp f.hom.toLinearMap) right +
            right • (D.toLinearMap.comp f.hom.toLinearMap) left := sorry
    exact
      { toLinearMap := D.toLinearMap.comp f.hom.toLinearMap
        map_one_eq_zero' := by
          change D (f.hom 1) = 0
          rw [map_one, Derivation.map_one_eq_zero]
        leibniz' := leibniz }
  map_add' := by
    intro first second
    apply Derivation.ext
    intro element
    rfl
  map_smul' := by
    intro scalar derivation
    apply Derivation.ext
    intro element
    rfl

/-- Restricting a residue derivation evaluates by precomposition with the underlying
algebra map. -/
theorem mapDerivation_apply {R S : CompleteLocalAlgCat Λ k} (f : Hom R S)
    (D : Derivation Λ S.carrier k) (x : R.carrier) :
    mapDerivation f D x = D (f.hom x) :=
  rfl

/-- A complete local algebra morphism is surjective if restriction of base-algebra
derivations into the identified residue field is injective. -/
@[stacks 06SD]
theorem surjective_of_mapDerivation_injective {R S : CompleteLocalAlgCat Λ k} (f : R ⟶ S)
    (hf : Function.Injective (mapDerivation f)) : Function.Surjective f.hom :=
  sorry

end Hom
end CompleteLocalAlgCat
