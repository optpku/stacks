module

public import stacks_project.Chap64.Definition_64_18_1_ZEllSheaf
public import Mathlib.Data.Complex.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Images
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.Tactic.CrossRefAttribute

/-!
# Multiplication by `ℓ` on the constant `ℤ_[ℓ]`-sheaf

On `X = Spec (CommRingCat.of ℂ)`, multiplication by `ℓ` on the constant `ℤ_[ℓ]`-sheaf has
stage maps `ℓ • 𝟙` on the constant sheaves of `ZMod (ℓ ^ n)`. The naive kernel inverse
system is the constant `ZMod ℓ` tower with zero transitions, so `Ker` of this morphism is
the zero system.
-/

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

/-- The constant étale abelian sheaf functor preserves finite limits, hence kernels. -/
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

/-- The coefficient map sending the class of `k * ℓ ^ n` in
`ker (ℓ • 𝟙)` on `ZMod (ℓ ^ (n + 1))` to `k` in `ZMod ℓ`. -/
def constantMulBy_nsmulKerHom (ℓ n : ℕ) :
    (constantMulBy_coeffNsmul.{u} ℓ n).hom.ker →+ ULift.{u} (ZMod ℓ) where
  toFun := fun y ↦
    ULift.up (Nat.cast (ZMod.val (ULift.down (Subtype.val y)) / ℓ ^ n) : ZMod ℓ)
  map_zero' := sorry
  map_add' := sorry

/-- After identifying the categorical kernel with `AddMonoidHom.ker`, the coefficient
kernel map is `constantMulBy_nsmulKerHom`. -/
def constantMulBy_kernelStageCoeff (ℓ n : ℕ) :
    kernel (constantMulBy_coeffNsmul.{u} ℓ n) ⟶
      AddCommGrpCat.of (ULift.{u} (ZMod ℓ)) :=
  (AddCommGrpCat.kernelIsoKer (constantMulBy_coeffNsmul.{u} ℓ n)).hom ≫
    AddCommGrpCat.ofHom (constantMulBy_nsmulKerHom ℓ n)

/-- `constantMulBy_nsmulKerHom` recovers the coefficient of `ℓ ^ n` in the kernel. -/
theorem constantMulBy_nsmulKerHom_spec (ℓ n : ℕ)
    (y : (constantMulBy_coeffNsmul.{u} ℓ n).hom.ker) :
    (ℓ ^ n : ZMod (ℓ ^ (n + 1))) * ZMod.cast (ULift.down (constantMulBy_nsmulKerHom ℓ n y)) =
      ULift.down (Subtype.val y) :=
  sorry

section

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact (Nat.Prime ℓ)] [IsNoetherian X]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{u}]

/-- Multiplication by `ℓ` on the constant `ℤ_[ℓ]`-sheaf, as a morphism of inverse systems.
This is the morphism `Φ` of the source example. -/
def constantMulBy : Hom (constant X ℓ) (constant X ℓ) where
  app n :=
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
      (constantMulBy_coeffNsmul ℓ n.unop)
  naturality := sorry

/-- Stage maps of `constantMulBy` are multiplication by `ℓ` on the constant `ZMod` stages. -/
theorem constantMulBy_app (n : ℕ) :
    hom_app (constantMulBy X ℓ) n = (ℓ : ℕ) • 𝟙 ((constant X ℓ).stage n) :=
  sorry

/-- The naive inverse system of stagewise kernels of `constantMulBy`. -/
abbrev constantMulBy_kernelSystem :
    SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  kernel (constantMulBy X ℓ)

/-- Stage `n` of the naive kernel system is the kernel of the stage-`n` map of `constantMulBy`. -/
def constantMulBy_kernelSystem_objIso (n : ℕ) :
    (constantMulBy_kernelSystem X ℓ).family n ≅
      kernel (hom_app (constantMulBy X ℓ) n) :=
  PreservesKernel.iso
    ((CategoryTheory.evaluation ℕᵒᵖ (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})).obj (op n))
    (constantMulBy X ℓ)

/-- The comparison from the naive kernel stage to the constant sheaf of `ZMod ℓ`. -/
def constantMulBy_kernelStageHom (n : ℕ) :
    (constantMulBy_kernelSystem X ℓ).family n ⟶
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} (ZMod ℓ))) :=
  (constantMulBy_kernelSystem_objIso X ℓ n).hom ≫
    (PreservesKernel.iso
        (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (constantMulBy_coeffNsmul ℓ n)).inv ≫
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map
        (constantMulBy_kernelStageCoeff ℓ n)

/-- Each naive kernel stage is isomorphic to the constant sheaf of `ZMod ℓ`. -/
theorem isIso_constantMulBy_kernelStageHom (n : ℕ) :
    IsIso (constantMulBy_kernelStageHom X ℓ n) :=
  sorry

/-- Images of successor maps in the naive kernel system vanish. -/
theorem constantMulBy_kernel_image_isZero (n : ℕ) :
    IsZero (Limits.image ((constantMulBy_kernelSystem X ℓ).stepMap n)) :=
  sorry

/-- The cokernel of the naive-kernel transition from stage `n + k` to stage `n`. -/
def constantMulBy_kernelTransitionCokernel (n k : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  cokernel ((constantMulBy_kernelSystem X ℓ).transitionMap (Nat.le_add_left n k))

/-- The map from naive kernel stage `n` to the product of cokernels of all later transitions.
Its kernel is the stable image intersection of images of naive-kernel transitions into stage `n`. -/
def constantMulBy_stableImageToCokernelProduct (n : ℕ) :
    (constantMulBy_kernelSystem X ℓ).family n ⟶
      ∏ᶜ fun k : ℕ ↦ constantMulBy_kernelTransitionCokernel X ℓ n k :=
  Pi.lift fun k ↦
    cokernel.π ((constantMulBy_kernelSystem X ℓ).transitionMap (Nat.le_add_left n k))

/-- Stage `n` of the stable-image tower of `constantMulBy`, i.e. the intersection of images of
transitions from later naive kernel stages. -/
def constantMulBy_kerStage (n : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} :=
  kernel (constantMulBy_stableImageToCokernelProduct X ℓ n)

/-- Successor maps of the stable-image tower are zero, since every naive-kernel successor is zero. -/
def constantMulBy_kerStepMap (n : ℕ) :
    constantMulBy_kerStage X ℓ (n + 1) ⟶ constantMulBy_kerStage X ℓ n :=
  0

/-- The stable-image inverse system of `constantMulBy`. This is the input to which
Lemma 64.18.3 is applied to obtain `Ker(Φ)`. -/
def constantMulBy_kerSystem :
    SequentialInverseSystem (Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) :=
  Functor.ofOpSequence (constantMulBy_kerStepMap X ℓ)

/-- Stage `n` of `constantMulBy_kerSystem` is the named stable-image object. -/
theorem constantMulBy_kerSystem_obj (n : ℕ) :
    (constantMulBy_kerSystem X ℓ).family n = constantMulBy_kerStage X ℓ n :=
  sorry

/-- Successor maps of `constantMulBy_kerSystem` are the named zero maps. -/
theorem constantMulBy_kerSystem_stepMap (n : ℕ) :
    (constantMulBy_kerSystem X ℓ).stepMap n = constantMulBy_kerStepMap X ℓ n :=
  sorry

/-- Each stable-image stage is the zero sheaf, because every successor of the naive kernel
system is zero and thus every image of a transition from a strictly later stage vanishes. -/
theorem constantMulBy_kerStage_isZero (n : ℕ) :
    IsZero (constantMulBy_kerStage X ℓ n) :=
  sorry

/-- The stable-image inverse system of `constantMulBy` is the zero system. -/
theorem constantMulBy_kerSystem_isZero :
    IsZero (constantMulBy_kerSystem X ℓ) :=
  sorry

end

variable (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
variable [HasSheafify (Spec (CommRingCat.of ℂ)).smallEtaleTopology AddCommGrpCat.{0}]
variable [∀ (Y : Scheme.{0}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{0}]

/-- Example 64.18.4 (1): on `X = Spec (CommRingCat.of ℂ)`, the morphism `Φ` of the
constant `ℤ_[ℓ]`-sheaf given by multiplication by `ℓ` has source component `n ≥ 1`
equal to `ℓ • 𝟙` on the constant sheaf of `ZMod (ℓ ^ n)`. -/
@[stacks 03UP]
theorem constantMulBy_component (n : ℕ+) :
    hom_app (constantMulBy (Spec (CommRingCat.of ℂ)) ℓ) n.natPred =
      (ℓ : ℕ) • 𝟙 ((constant (Spec (CommRingCat.of ℂ)) ℓ).component n) :=
  sorry

/-- Example 64.18.4 (2): on `X = Spec (CommRingCat.of ℂ)`, for every source index `n ≥ 1`
the naive kernel stage of `Φ` is isomorphic to the constant sheaf of `ULift (ZMod ℓ)`
via `constantMulBy_kernelStageHom`. -/
@[stacks 03UP]
theorem isIso_constantMulBy_kernelStageHom_component (n : ℕ+) :
    IsIso (constantMulBy_kernelStageHom (Spec (CommRingCat.of ℂ)) ℓ n.natPred) :=
  sorry

/-- Example 64.18.4 (3): on `X = Spec (CommRingCat.of ℂ)`, every successor of the naive
kernel inverse system of `Φ` is the zero morphism. -/
@[stacks 03UP]
theorem constantMulBy_kernel_stepMap_eq_zero (n : ℕ) :
    (constantMulBy_kernelSystem (Spec (CommRingCat.of ℂ)) ℓ).stepMap n = 0 :=
  sorry

/-- Example 64.18.4 (4): on `X = Spec (CommRingCat.of ℂ)`, each stable-image stage of `Φ`
(the intersection of images of naive-kernel transitions into that stage) is the zero sheaf. -/
@[stacks 03UP]
theorem constantMulBy_kerStage_isZero_component (n : ℕ) :
    IsZero (constantMulBy_kerStage (Spec (CommRingCat.of ℂ)) ℓ n) :=
  sorry

/-- Example 64.18.4 (5): since those stable-image stages vanish, `Ker(Φ)` is the zero
inverse system. -/
@[stacks 03UP]
theorem constantMulBy_ker_isZeroSystem :
    IsZero (constantMulBy_kerSystem (Spec (CommRingCat.of ℂ)) ℓ) :=
  sorry

end ZEllSheaf
end AlgebraicGeometry.Scheme.Etale
