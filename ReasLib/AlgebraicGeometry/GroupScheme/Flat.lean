/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

@[expose] public section

open CategoryTheory
open MonoidalCategory MonObj CartesianMonoidalCategory

universe u

namespace AlgebraicGeometry.GroupScheme

/-- Left translation by a morphism from a flat scheme to a group scheme is flat. -/
instance instFlatMulLeft {S : Scheme.{u}} (G : Over S) [GrpObj G] (T : Over S)
    [Flat T.hom] (ψ : T ⟶ G) : Flat (((ψ ⊗ₘ 𝟙 G) ≫ μ[G]).left) := by
  let e : T ⊗ G ≅ T ⊗ G := {
    hom := lift (fst T G) ((fst T G ≫ ψ) * snd T G)
    inv := lift (fst T G) ((fst T G ≫ ψ)⁻¹ * snd T G)
    hom_inv_id := by
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · set f : T ⊗ G ⟶ G := fst T G ≫ ψ
        simp only [Category.assoc, lift_snd]
        rw [MonObj.comp_mul]
        have hfinv : lift (fst T G) (f * snd T G) ≫ f⁻¹ = f⁻¹ := by
          simp [GrpObj.comp_inv, f]
        have hsnd : lift (fst T G) (f * snd T G) ≫ snd T G = f * snd T G := by
          simp [f]
        rw [hfinv, hsnd]
        simp [f]
    inv_hom_id := by
      apply CartesianMonoidalCategory.hom_ext
      · simp
      · set f : T ⊗ G ⟶ G := fst T G ≫ ψ
        simp only [Category.assoc, lift_snd]
        rw [MonObj.comp_mul]
        have hf : lift (fst T G) (f⁻¹ * snd T G) ≫ f = f := by
          simp [f]
        have hsnd : lift (fst T G) (f⁻¹ * snd T G) ≫ snd T G = f⁻¹ * snd T G := by
          simp [f]
        rw [hf, hsnd]
        simp [f] }
  have htensor : ψ ▷ G = lift (fst T G ≫ ψ) (snd T G) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hmul : e.hom ≫ snd T G = (ψ ⊗ₘ 𝟙 G) ≫ μ[G] := by
    calc
      e.hom ≫ snd T G = fst T G ≫ ψ * snd T G := by simp [e]
      _ = lift (fst T G ≫ ψ) (snd T G) ≫ μ[G] := rfl
      _ = (ψ ⊗ₘ 𝟙 G) ≫ μ[G] := by
        change lift (fst T G ≫ ψ) (snd T G) ≫ μ[G] = (ψ ▷ G) ≫ μ[G]
        simpa using congrArg (fun f ↦ f ≫ μ[G]) htensor.symm
  let e' := (Over.forget S).mapIso e
  have hmul_left : e'.hom ≫ (snd T G).left = (((ψ ⊗ₘ 𝟙 G) ≫ μ[G]).left) := by
    simpa [e'] using congrArg Over.Hom.left hmul
  rw [← hmul_left]
  change Flat (e'.hom ≫ (snd T G).left)
  rw [MorphismProperty.cancel_left_of_respectsIso @Flat e'.hom (snd T G).left]
  change Flat (Limits.pullback.snd T.hom G.hom)
  infer_instance

/-- The multiplication morphism of a flat group scheme is flat. -/
instance instFlatMul {S : Scheme.{u}} (G : Over S) [GrpObj G] [Flat G.hom] :
    Flat (μ[G].left) := by
  simpa using (instFlatMulLeft G G (𝟙 G))

end AlgebraicGeometry.GroupScheme
