module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.EllAdicSheaf.Kernels

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The constant functor into étale abelian presheaves preserves finite limits. -/
instance instPreservesFiniteLimits_constEtaleAbelian (X : Scheme.{u}) :
    PreservesFiniteLimits
      (Functor.const (X.Etale)ᵒᵖ :
        AddCommGrpCat.{u} ⥤ (X.Etale)ᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  inferInstance

/-- The constant étale abelian sheaf functor preserves finite limits. -/
instance instPreservesFiniteLimits_constantEtaleAbelianSheaf (X : Scheme.{u})
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}] :
    PreservesFiniteLimits (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  comp_preservesFiniteLimits
    (Functor.const (X.Etale)ᵒᵖ)
    (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u})

namespace ZEllSheaf

/-- Multiplication by `ℓ` on the coefficient group `ULift (ZMod (ℓ ^ (n + 1)))`. -/
def constantMulBy_coeffNsmul (ℓ n : ℕ) :
    AddCommGrpCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1)))) ⟶
      AddCommGrpCat.of (ULift.{u} (ZMod (ℓ ^ (n + 1)))) :=
  (ℓ : ℕ) • 𝟙 _

/-- The coefficient homomorphism from the kernel of multiplication by `ℓ` to `ZMod ℓ`. -/
def constantMulBy_nsmulKerHom (ℓ n : ℕ) :
    (constantMulBy_coeffNsmul.{u} ℓ n).hom.ker →+ ULift.{u} (ZMod ℓ) where
  toFun := fun y ↦
    ULift.up (Nat.cast (ZMod.val (ULift.down (Subtype.val y)) / ℓ ^ n) : ZMod ℓ)
  map_zero' := sorry
  map_add' := sorry

/-- The coefficient-kernel morphism induced by `constantMulBy_nsmulKerHom`. -/
def constantMulBy_kernelStageCoeff (ℓ n : ℕ) :
    kernel (constantMulBy_coeffNsmul.{u} ℓ n) ⟶
      AddCommGrpCat.of (ULift.{u} (ZMod ℓ)) :=
  (AddCommGrpCat.kernelIsoKer (constantMulBy_coeffNsmul.{u} ℓ n)).hom ≫
    AddCommGrpCat.ofHom (constantMulBy_nsmulKerHom ℓ n)

/-- Multiplication by `ℓ ^ n` recovers a kernel element after coefficient division, for `ℓ > 0`. -/
theorem constantMulBy_nsmulKerHom_spec (ℓ n : ℕ) (hℓ : 0 < ℓ)
    (y : (constantMulBy_coeffNsmul.{u} ℓ n).hom.ker) :
    (ℓ ^ n : ZMod (ℓ ^ (n + 1))) *
        ZMod.cast (ULift.down (constantMulBy_nsmulKerHom ℓ n y)) =
      ULift.down (Subtype.val y) :=
  sorry

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- Multiplication by `ℓ` on the constant `ℤ_[ℓ]`-sheaf. -/
def constantMulBy : Hom (constant X ℓ) (constant X ℓ) :=
  homMk
    { app := fun n ↦
        (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
          (constantMulBy_coeffNsmul ℓ n.unop)
      naturality := by sorry }

/-- The naturality law for the stage maps of `constantMulBy`. -/
theorem constantMulBy_naturality (n : ℕ) :
    hom_app (constantMulBy X ℓ) (n + 1) ≫ (constant X ℓ).stepMap n =
      (constant X ℓ).stepMap n ≫ hom_app (constantMulBy X ℓ) n :=
  sorry

/-- Each stage map of `constantMulBy` is scalar multiplication by `ℓ`. -/
theorem constantMulBy_app (n : ℕ) :
    hom_app (constantMulBy X ℓ) n = (ℓ : ℕ) • 𝟙 ((constant X ℓ).stage n) :=
  sorry

/-- The comparison from a naive kernel stage to the constant `ZMod ℓ`-sheaf. -/
def constantMulBy_kernelStageHom (n : ℕ) :
    (naiveKerSystem (constantMulBy X ℓ)).family n ⟶
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod ℓ))) :=
  (naiveKerSystem_objIso (constantMulBy X ℓ) n).hom ≫
    (PreservesKernel.iso
        (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (constantMulBy_coeffNsmul ℓ n)).inv ≫
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (constantMulBy_kernelStageCoeff ℓ n)

/-- Every naive kernel stage is canonically isomorphic to the constant `ZMod ℓ`-sheaf. -/
instance isIso_constantMulBy_kernelStageHom (n : ℕ) :
    IsIso (constantMulBy_kernelStageHom X ℓ n) := by
  sorry

/-- Images of successor maps in the naive kernel system vanish. -/
theorem constantMulBy_kernel_image_isZero (n : ℕ) :
    IsZero (Limits.image ((naiveKerSystem (constantMulBy X ℓ)).stepMap n)) :=
  sorry

/-- The successor map of the naive kernel system is zero. -/
theorem constantMulBy_naiveKerSystem_stepMap_eq_zero (n : ℕ) :
    (naiveKerSystem (constantMulBy X ℓ)).stepMap n = 0 :=
  sorry

/-- Each stable-image stage of the canonical kernel construction is zero. -/
theorem constantMulBy_stableImageStage_isZero (n : ℕ) :
    IsZero (stableImageStage (constantMulBy X ℓ) n) :=
  sorry

/-- The canonical stable-image system of `constantMulBy` is zero. -/
theorem constantMulBy_stableImageSystem_isZero :
    IsZero (stableImageSystem (constantMulBy X ℓ)) :=
  sorry

/-- The actual `ℓ`-adic kernel of `constantMulBy` is zero. -/
theorem constantMulBy_ker_isZeroSystem :
    IsZero (ker (constantMulBy X ℓ)) :=
  sorry

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
