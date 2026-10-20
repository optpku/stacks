/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
public import Mathlib.NumberTheory.Padics.RingHoms
public import stacks_project.Chap64.Definition_64_18_1_ZEllSheaf
public import stacks_project.Chap64.Lemma_64_18_3_Category

/-!
# Torsion ℤ_[ℓ]-sheaves and Hom of ℚ_[ℓ]-sheaves

A `ℤ_[ℓ]`-sheaf is torsion when some power `ℓ ^ n • 𝟙` vanishes. Morphisms of
`ℚ_[ℓ]`-sheaves are morphisms of `ℤ_[ℓ]`-sheaves after extending scalars from
`ℤ_[ℓ]` to `ℚ_[ℓ]`; the quotient functor is the identity on objects and this
scalar extension on morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped ChangeOfRings

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace ZEllSheaf

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- The endomorphism `ℓ ^ n : F ⟶ F` of a `ℤ_[ℓ]`-sheaf. -/
def nsmulHom (F : ZEllSheaf X ℓ) (n : ℕ) : Hom F F :=
  (ℓ ^ n) • 𝟙 F

/-- Stage components of `ℓ ^ n : F ⟶ F` are multiplication by `ℓ ^ n` on each stage. -/
theorem nsmulHom_app (F : ZEllSheaf X ℓ) (n k : ℕ) :
    hom_app (nsmulHom F n) k = (ℓ ^ n) • 𝟙 (F.stage k) := sorry

/-- A `ℤ_[ℓ]`-sheaf is torsion when `ℓ ^ n : F ⟶ F` vanishes for some `n`. -/
def IsTorsion (F : ZEllSheaf X ℓ) : Prop :=
  ∃ n : ℕ, nsmulHom F n = 0

/-- Torsion is vanishing of some power `ℓ ^ n • 𝟙` on every stage. -/
theorem isTorsion_iff (F : ZEllSheaf X ℓ) :
    F.IsTorsion ↔ ∃ n : ℕ, ∀ k : ℕ, (ℓ ^ n) • 𝟙 (F.stage k) = 0 := sorry

/-- The object property of torsion `ℤ_[ℓ]`-sheaves. -/
def torsion : ObjectProperty (ZEllSheaf X ℓ) :=
  fun F ↦ F.IsTorsion

/-- The torsion object property is the predicate `IsTorsion`. -/
theorem torsion_iff (F : ZEllSheaf X ℓ) :
    torsion F ↔ F.IsTorsion := sorry

/-- Scalar multiplication by a `ℤ_[ℓ]`-integer on a morphism of `ℤ_[ℓ]`-sheaves,
via compatible residue nsmul on each stage. -/
def homSMul {F G : ZEllSheaf X ℓ} (a : ℤ_[ℓ]) (f : Hom F G) : Hom F G :=
  homMk
    { app := fun n ↦ (PadicInt.toZModPow (n.unop + 1) a).val • (hom f).app n
      naturality := by sorry }

/-- Stage components of padic scalar multiplication are residue nsmul of the
stage maps. -/
theorem homSMul_app {F G : ZEllSheaf X ℓ} (a : ℤ_[ℓ]) (f : Hom F G) (n : ℕ) :
    (hom (homSMul a f)).app (op n) =
      (PadicInt.toZModPow (n + 1) a).val • (hom f).app (op n) := sorry

/-- Hom-groups of `ℤ_[ℓ]`-sheaves are `ℤ_[ℓ]`-modules via residue nsmul. -/
instance instModuleHom (F G : ZEllSheaf X ℓ) : Module ℤ_[ℓ] (Hom F G) where
  smul := homSMul
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- The category of `ℤ_[ℓ]`-sheaves is `ℤ_[ℓ]`-linear. -/
instance instLinear : Linear ℤ_[ℓ] (ZEllSheaf X ℓ) where
  homModule := instModuleHom
  smul_comp := sorry
  comp_smul := sorry

/-- Torsion `ℤ_[ℓ]`-sheaves form a Serre class, once the ambient category is abelian. -/
instance instIsSerreClass_torsion [Abelian (ZEllSheaf X ℓ)] :
    (torsion : ObjectProperty (ZEllSheaf X ℓ)).IsSerreClass := sorry

/-- The Hom-object of `ℚ_[ℓ]`-sheaves, as `Hom_{ℤ_[ℓ]}(F, G) ⊗[ℤ_[ℓ]] ℚ_[ℓ]`. -/
def qellHom (F G : ZEllSheaf X ℓ) : ModuleCat ℚ_[ℓ] :=
  (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
    (ModuleCat.of ℤ_[ℓ] (Hom F G))

/-- Unfolding of `qellHom` as extension of scalars of the `ℤ_[ℓ]`-Hom module. -/
theorem qellHom_eq (F G : ZEllSheaf X ℓ) :
    qellHom F G =
      (ModuleCat.extendScalars (algebraMap ℤ_[ℓ] ℚ_[ℓ])).obj
        (ModuleCat.of ℤ_[ℓ] (Hom F G)) := sorry

/-- The quotient functor `F ↦ F ⊗ ℚ_[ℓ]` on morphisms, sending `f` to `1 ⊗ₜ f`. -/
def tensorQEll {F G : ZEllSheaf X ℓ} (f : Hom F G) : qellHom F G :=
  (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] f

/-- `tensorQEll f` is the canonical image of `f` in `Hom ⊗[ℤ_[ℓ]] ℚ_[ℓ]`. -/
theorem tensorQEll_apply {F G : ZEllSheaf X ℓ} (f : Hom F G) :
    tensorQEll f = (1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] f := sorry

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
