/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ConstantMulByKernel
import StacksCheckRecall

/-!
# Multiplication by `ℓ` on the constant `ℤ_[ℓ]`-sheaf

The source-facing checks for Example 64.18.4 use the generalized construction in `ReasLib`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive Opposite
open CategoryTheory.Sheaf

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale.ZEllSheaf

variable (ℓ : ℕ) [Fact (Nat.Prime ℓ)]
variable [HasSheafify (Spec (CommRingCat.of ℂ)).smallEtaleTopology AddCommGrpCat.{0}]
variable [∀ (Y : Scheme.{0}) (V : Y.Etale),
    HasWeakSheafify (Y.smallEtaleTopology.over V) AddCommGrpCat.{0}]

/-! Example 64.18.4 -/
@[stacks 03UP] #check
  (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.constantMulBy_ker_isZeroSystem
    (X := Spec (CommRingCat.of ℂ)) (ℓ := ℓ) :
    IsZero (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.ker
      (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.constantMulBy
        (Spec (CommRingCat.of ℂ)) ℓ)))

/- Example 64.18.4 (1): each stage map of multiplication by `ℓ` is `ℓ • 𝟙`. -/
@[stacks 03UP]
#check
  (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.constantMulBy_app
    (X := Spec (CommRingCat.of ℂ)) (ℓ := ℓ) :
    ∀ n : ℕ,
      hom_app (constantMulBy (Spec (CommRingCat.of ℂ)) ℓ) n =
        (ℓ : ℕ) • 𝟙 ((constant (Spec (CommRingCat.of ℂ)) ℓ).stage n))

/- Example 64.18.4 (2): each naive kernel stage is isomorphic to the constant `ZMod ℓ`-sheaf. -/
@[stacks 03UP]
#check
  (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.isIso_constantMulBy_kernelStageHom
    (X := Spec (CommRingCat.of ℂ)) (ℓ := ℓ) :
    ∀ n : ℕ, IsIso (constantMulBy_kernelStageHom (Spec (CommRingCat.of ℂ)) ℓ n))

/- Example 64.18.4 (3): every successor of the naive kernel system is zero. -/
@[stacks 03UP]
#check
  (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.constantMulBy_naiveKerSystem_stepMap_eq_zero
    (X := Spec (CommRingCat.of ℂ)) (ℓ := ℓ) :
    ∀ n : ℕ,
      (naiveKerSystem (constantMulBy (Spec (CommRingCat.of ℂ)) ℓ)).stepMap n = 0)

/- Example 64.18.4 (4): every stable-image stage is the zero sheaf. -/
@[stacks 03UP]
#check
  (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.constantMulBy_stableImageStage_isZero
    (X := Spec (CommRingCat.of ℂ)) (ℓ := ℓ) :
    ∀ n : ℕ,
      IsZero (stableImageStage (constantMulBy (Spec (CommRingCat.of ℂ)) ℓ) n))

/- Example 64.18.4 (5): the stable-image system is zero. -/
@[stacks 03UP]
#check
  (AlgebraicGeometry.Scheme.Etale.ZEllSheaf.constantMulBy_stableImageSystem_isZero
    (X := Spec (CommRingCat.of ℂ)) (ℓ := ℓ) :
    IsZero (stableImageSystem (constantMulBy (Spec (CommRingCat.of ℂ)) ℓ)))

end AlgebraicGeometry.Scheme.Etale.ZEllSheaf
