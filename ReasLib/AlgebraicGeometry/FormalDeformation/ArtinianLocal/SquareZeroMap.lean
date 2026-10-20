/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.ArtinianLocal.SquareZero

/-!
# Linear maps of square-zero extensions

Linear maps of coefficient spaces induce residue-compatible morphisms of their
trivial square-zero extensions.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

variable {V W U : Type u} [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup W] [Module k W] [Module.Finite k W]
  [AddCommGroup U] [Module k U] [Module.Finite k U]

/-- A linear map of coefficient spaces induces a morphism of square-zero extensions. -/
noncomputable def squareZeroMap (linearMap : V →ₗ[k] W) :
    squareZero Λ k V ⟶ squareZero Λ k W := by
  let hom : algebraHom (squareZero Λ k V) (squareZero Λ k W) :=
    (TrivSqZeroExt.map linearMap).restrictScalars Λ
  have laws : IsLocalHom hom ∧
      (∀ localness : IsLocalHom hom,
        residueCompat (A := squareZero Λ k V) (B := squareZero Λ k W) hom localness =
          residueIsoHom (squareZero Λ k V)) := by
    sorry
  exact Hom.of hom laws.1 (laws.2 laws.1)

/-- The algebra map induced on square-zero extensions is the standard coefficient map. -/
theorem squareZeroMap_hom (linearMap : V →ₗ[k] W) :
    (squareZeroMap linearMap : squareZero Λ k V ⟶ squareZero Λ k W).hom =
      (TrivSqZeroExt.map linearMap).restrictScalars Λ := rfl

/-- The identity coefficient map induces the identity square-zero morphism. -/
theorem squareZeroMap_id (V : Type u) [AddCommGroup V] [Module k V] [Module.Finite k V] :
    squareZeroMap (LinearMap.id : V →ₗ[k] V) = 𝟙 (squareZero Λ k V) := sorry

/-- Composition of coefficient maps agrees with composition of square-zero morphisms. -/
theorem squareZeroMap_comp (linearMap : V →ₗ[k] W) (nextMap : W →ₗ[k] U) :
    (squareZeroMap (nextMap.comp linearMap) : squareZero Λ k V ⟶ squareZero Λ k U) =
      squareZeroMap linearMap ≫ squareZeroMap nextMap := sorry

end ArtinianLocalAlgCat
