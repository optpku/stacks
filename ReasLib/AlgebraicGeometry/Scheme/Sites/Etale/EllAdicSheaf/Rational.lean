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
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

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
open scoped ChangeOfRings TensorProduct

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

namespace AlgebraicGeometry.Scheme.Etale

/-- Rational ℓ-adic sheaves are represented by integral ℓ-adic sheaves,
with morphisms extended to the fraction field of the ℓ-adic integers. -/
def QEllSheaf (X : Scheme.{u}) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] [IsNoetherian X]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [∀ (Y : Scheme.{u}) (V : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}] :=
  ZEllSheaf X ℓ

variable {X : Scheme.{u}} {ℓ : ℕ} [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

namespace ZEllSheaf

/-- Bilinear extension of composition to the rationalized Hom modules. -/
def qellComp (F G H : ZEllSheaf X ℓ) (f : qellHom F G) (g : qellHom G H) :
    qellHom F H :=
  (TensorProduct.map₂ (LinearMap.mul ℤ_[ℓ] ℚ_[ℓ]) (Linear.comp F G H) :
    (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (F ⟶ G)) →ₗ[ℤ_[ℓ]]
      (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (G ⟶ H)) →ₗ[ℤ_[ℓ]]
        (ℚ_[ℓ] ⊗[ℤ_[ℓ]] (F ⟶ H))) f g

/-- On pure tensors, composition multiplies coefficients and composes sheaf maps. -/
theorem qellComp_tmul {F G H : ZEllSheaf X ℓ} (a b : ℚ_[ℓ])
    (f : F ⟶ G) (g : G ⟶ H) :
    qellComp F G H
        (a ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] f)
        (b ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] g) =
      (a * b) ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] (f ≫ g) := sorry

end ZEllSheaf

namespace QEllSheaf

/-- The integral sheaf representing an object of the rationalized category. -/
def toZEllSheaf (F : QEllSheaf X ℓ) : ZEllSheaf X ℓ := F

/-- Regard an integral sheaf as an object of the rationalized category. -/
def ofZEllSheaf (F : ZEllSheaf X ℓ) : QEllSheaf X ℓ := F

/-- Rationalization retains the integral representative on objects. -/
theorem toZEllSheaf_ofZEllSheaf (F : ZEllSheaf X ℓ) :
    toZEllSheaf (ofZEllSheaf F) = F := sorry

/-- Every rational sheaf is represented by its underlying integral sheaf. -/
theorem ofZEllSheaf_toZEllSheaf (F : QEllSheaf X ℓ) :
    ofZEllSheaf (toZEllSheaf F) = F := sorry

/-- Hom groups are extended from ℤ_[ℓ] to ℚ_[ℓ],
with identity `1 ⊗ 𝟙` and composition induced by integral composition. -/
instance instCategory : Category (QEllSheaf X ℓ) where
  Hom F G := ZEllSheaf.qellHom (toZEllSheaf F) (toZEllSheaf G)
  id F := ZEllSheaf.tensorQEll (𝟙 (toZEllSheaf F))
  comp {F G H} f g := ZEllSheaf.qellComp (toZEllSheaf F) (toZEllSheaf G) (toZEllSheaf H) f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The Hom groups carry the additive structure of their tensor products. -/
instance instPreadditive : Preadditive (QEllSheaf X ℓ) where
  homGroup F G := inferInstanceAs
    (AddCommGroup (ZEllSheaf.qellHom (toZEllSheaf F) (toZEllSheaf G)))
  add_comp := sorry
  comp_add := sorry

/-- Rationalized composition is ℚ_[ℓ]-bilinear. -/
instance instLinear : Linear ℚ_[ℓ] (QEllSheaf X ℓ) where
  homModule F G := inferInstanceAs
    (Module ℚ_[ℓ] (ZEllSheaf.qellHom (toZEllSheaf F) (toZEllSheaf G)))
  smul_comp := sorry
  comp_smul := sorry

/-- The identity in the rationalized category is the image of the integral identity. -/
theorem id_eq (F : QEllSheaf X ℓ) :
    𝟙 F = ZEllSheaf.tensorQEll (𝟙 (toZEllSheaf F)) := sorry

/-- Composition of pure-tensor morphisms in the rationalized category. -/
theorem comp_tmul {F G H : QEllSheaf X ℓ} (a b : ℚ_[ℓ])
    (f : toZEllSheaf F ⟶ toZEllSheaf G) (g : toZEllSheaf G ⟶ toZEllSheaf H) :
    ((a ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] f : F ⟶ G) ≫
        (b ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] g : G ⟶ H) : F ⟶ H) =
      (a * b) ⊗ₜ[ℤ_[ℓ], algebraMap ℤ_[ℓ] ℚ_[ℓ]] (f ≫ g) := sorry

end QEllSheaf

namespace ZEllSheaf

/-- The quotient functor `F ↦ F ⊗ ℚ_[ℓ]`,
retaining objects and sending a morphism `f` to `1 ⊗ f`. -/
def tensorQEllFunctor : ZEllSheaf X ℓ ⥤ QEllSheaf X ℓ where
  obj := QEllSheaf.ofZEllSheaf
  map f := tensorQEll f
  map_id := sorry
  map_comp := sorry

/-- On objects the quotient functor keeps the same integral representative. -/
theorem tensorQEllFunctor_obj (F : ZEllSheaf X ℓ) :
    (tensorQEllFunctor : ZEllSheaf X ℓ ⥤ QEllSheaf X ℓ).obj F =
      QEllSheaf.ofZEllSheaf F := sorry

/-- The quotient functor acts on morphisms by the existing tensor map. -/
theorem tensorQEllFunctor_map {F G : ZEllSheaf X ℓ} (f : F ⟶ G) :
    (tensorQEllFunctor : ZEllSheaf X ℓ ⥤ QEllSheaf X ℓ).map f = tensorQEll f := sorry

/-- The rationalization functor preserves addition of morphisms. -/
instance tensorQEllFunctor_additive :
    (tensorQEllFunctor : ZEllSheaf X ℓ ⥤ QEllSheaf X ℓ).Additive := sorry

/-- Rationalization is localization at morphisms with torsion kernel and cokernel. -/
instance tensorQEllFunctor_isLocalization :
    (tensorQEllFunctor : ZEllSheaf X ℓ ⥤ QEllSheaf X ℓ).IsLocalization
      (torsion : ObjectProperty (ZEllSheaf X ℓ)).isoModSerre := sorry

end ZEllSheaf

namespace QEllSheaf

/-- Rational ℓ-adic sheaves form an abelian category, as the Serre quotient by torsion. -/
instance instAbelian : Abelian (QEllSheaf X ℓ) :=
  ObjectProperty.SerreClassLocalization.abelian
    (ZEllSheaf.tensorQEllFunctor : ZEllSheaf X ℓ ⥤ QEllSheaf X ℓ)
    (ZEllSheaf.torsion : ObjectProperty (ZEllSheaf X ℓ))

end QEllSheaf
end AlgebraicGeometry.Scheme.Etale
