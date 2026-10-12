/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.Normalization

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.FunctionFieldExtension

variable (X : Scheme.{u}) [IsIntegral X] (L : Type u) [Field L]
  [Algebra X.functionField L]

/-- The automorphism of `Spec L` induced by an `X.functionField`-algebra automorphism of `L`. -/
noncomputable def galoisSpec (σ : L ≃ₐ[X.functionField] L) :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L) :=
  Spec.map (CommRingCat.ofHom σ.toRingHom)

/-- An `X.functionField`-algebra automorphism of `L` preserves the canonical morphism to `X`. -/
theorem map_comp_galoisSpec (σ : L ≃ₐ[X.functionField] L) :
    galoisSpec X L σ ≫ map X L = map X L := by
  dsimp [galoisSpec, map, FieldExtension.specMap]
  have h :
      CommRingCat.ofHom (algebraMap X.functionField L) ≫
          CommRingCat.ofHom (↑σ : L →+* L) =
        CommRingCat.ofHom (algebraMap X.functionField L) := by
    apply CommRingCat.hom_ext
    ext x
    exact σ.commutes x
  rw [← Category.assoc, ← Spec.map_comp, h]

/-- The canonical morphism `Spec L ⟶ X` factors through the normalization after applying a
function-field automorphism to `Spec L`. -/
theorem galoisHom_factor (σ : L ≃ₐ[X.functionField] L) :
    map X L =
      (galoisSpec X L σ ≫ (map X L).toNormalization) ≫ (map X L).fromNormalization := by
  simp [Category.assoc, map_comp_galoisSpec]

/-- The automorphism of the normalization induced by an automorphism of its function field. -/
noncomputable def galoisHom (σ : L ≃ₐ[X.functionField] L) :
    (map X L).normalization ⟶ (map X L).normalization :=
  (map X L).normalizationDesc
    (galoisSpec X L σ ≫ (map X L).toNormalization)
    (map X L).fromNormalization
    (galoisHom_factor X L σ)

/-- The inertia subgroup at a point of the normalization consists of automorphisms fixing the
point and acting trivially on its residue field. -/
noncomputable def inertia (y : (map X L).normalization) :
    Subgroup (L ≃ₐ[X.functionField] L) where
  carrier :=
    {σ | galoisHom X L σ y = y ∧
      ∀ hy : galoisHom X L σ y = y,
        (galoisHom X L σ).residueFieldMap y =
          eqToHom (congrArg (Scheme.residueField (map X L).normalization) hy)}
  one_mem' := sorry
  mul_mem' := sorry
  inv_mem' := sorry

/-- Membership in the inertia subgroup is equivalent to fixed-point and residue-field conditions. -/
theorem mem_inertia_iff (y : (map X L).normalization) (σ : L ≃ₐ[X.functionField] L) :
    σ ∈ inertia X L y ↔
      galoisHom X L σ y = y ∧
        ∀ hy : galoisHom X L σ y = y,
          (galoisHom X L σ).residueFieldMap y =
            eqToHom (congrArg (Scheme.residueField (map X L).normalization) hy) := sorry

/-- The inertia subgroup at a point is trivial exactly when every one of its elements is the
identity automorphism. -/
theorem inertia_eq_bot_iff (y : (map X L).normalization) :
    inertia X L y = ⊥ ↔ ∀ σ : L ≃ₐ[X.functionField] L, σ ∈ inertia X L y → σ = 1 := sorry

end AlgebraicGeometry.Scheme.FunctionFieldExtension
