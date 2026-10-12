/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Action
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.CategoryTheory.InverseSystem.Cone
public import ReasLib.CategoryTheory.NatTrans.Arrow
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open SheafOfModules.RingedSite.IdealSheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.AdicLimit

variable {X : Scheme.{u}}

/-- The tail system whose stage `m` is the image of the action of `I ^ (n + 1)` on
`F.obj (op (n + m))`. -/
noncomputable def powerTailSystem (I : X.IdealSheafData)
    (F : SequentialInverseSystem X.Modules) (n : ℕ) :
    SequentialInverseSystem X.Modules :=
  F.shift n ⋙
    (SheafOfModules.RingedSite.IdealSheaf.powerActionNat I.toSubobject (n + 1)).imageFunctor

/-- Stage `m` of `powerTailSystem I F n` is the image of the `I ^ (n + 1)`-action on
`F.obj (op (n + m))`. -/
theorem powerTailSystem_obj (I : X.IdealSheafData)
    (F : SequentialInverseSystem X.Modules) (n m : ℕ) :
    (powerTailSystem I F n).obj (op m) =
      image (SheafOfModules.RingedSite.IdealSheaf.powerAction I.toSubobject
        (F.obj (op (n + m))) (n + 1)) := sorry

/-- The cone obtained by applying the `I ^ (n + 1)` image functor to the canonical limit cone
restricted to the tail beginning at `n`. -/
noncomputable def powerTailCone (I : X.IdealSheafData)
    (F : SequentialInverseSystem X.Modules) (n : ℕ) : Cone (powerTailSystem I F n) :=
  (SheafOfModules.RingedSite.IdealSheaf.powerActionNat I.toSubobject
    (n + 1)).imageFunctor.mapCone ((limit.cone F).shift n)

/-- The point of `powerTailCone I F n` is the image of the `I ^ (n + 1)`-action on
`limit F`. -/
theorem powerTailCone_pt (I : X.IdealSheafData)
    (F : SequentialInverseSystem X.Modules) (n : ℕ) :
    (powerTailCone I F n).pt =
      image (SheafOfModules.RingedSite.IdealSheaf.powerAction I.toSubobject
        (limit F : X.Modules) (n + 1)) := sorry

/-- The `m`th leg of `powerTailCone I F n` is the image of the corresponding limit
projection. -/
theorem powerTailCone_π_app (I : X.IdealSheafData)
    (F : SequentialInverseSystem X.Modules) (n m : ℕ) :
    (powerTailCone I F n).π.app (op m) =
      (SheafOfModules.RingedSite.IdealSheaf.powerActionNat I.toSubobject
        (n + 1)).imageFunctor.map (limit.π F (op (n + m))) := sorry

/-- The canonical comparison from `I ^ (n + 1)` acting on `limit F` to the limit of the
fixed-power tail system. -/
noncomputable def powerLimitComparison (I : X.IdealSheafData)
    (F : SequentialInverseSystem X.Modules) (n : ℕ) :
    (powerTailCone I F n).pt ⟶ limit (powerTailSystem I F n) :=
  limit.lift (powerTailSystem I F n) (powerTailCone I F n)

/-- Composing `powerLimitComparison I F n` with a limit projection gives the corresponding
leg of `powerTailCone I F n`. -/
theorem powerLimitComparison_fac (I : X.IdealSheafData)
    (F : SequentialInverseSystem X.Modules) (n m : ℕ) :
    powerLimitComparison I F n ≫ limit.π (powerTailSystem I F n) (op m) =
      (powerTailCone I F n).π.app (op m) := sorry

/-- The `I ^ (n + 1)`-action on `limit F` is killed by its projection to stage `n` when
successor kernels are the prescribed ideal-power images. -/
theorem powerAction_comp_limitProjection (I : X.IdealSheafData)
    (F : SequentialInverseSystem X.Modules)
    (h_kernel : ∀ k : ℕ, kernelSubobject (F.stepMap k) =
      imageSubobject (SheafOfModules.RingedSite.IdealSheaf.powerAction I.toSubobject
        (F.obj (op (k + 1))) (k + 1))) (n : ℕ) :
    SheafOfModules.RingedSite.IdealSheaf.powerAction I.toSubobject
        (limit F : X.Modules) (n + 1) ≫
      limit.π F (op n) = 0 := sorry

/-- The canonical map `(limit F) / I ^ (n + 1) (limit F) ⟶ F.obj (op n)` induced by the
limit projection. -/
noncomputable def stageComparison (I : X.IdealSheafData)
    (F : SequentialInverseSystem X.Modules)
    (h_kernel : ∀ k : ℕ, kernelSubobject (F.stepMap k) =
      imageSubobject (SheafOfModules.RingedSite.IdealSheaf.powerAction I.toSubobject
        (F.obj (op (k + 1))) (k + 1))) (n : ℕ) :
    cokernel (SheafOfModules.RingedSite.IdealSheaf.powerAction I.toSubobject
        (limit F : X.Modules) (n + 1)) ⟶ F.obj (op n) :=
  cokernel.desc
    (SheafOfModules.RingedSite.IdealSheaf.powerAction I.toSubobject
      (limit F : X.Modules) (n + 1))
    (limit.π F (op n)) (powerAction_comp_limitProjection I F h_kernel n)

/-- The quotient projection followed by `stageComparison I F h_kernel n` is the canonical
limit projection to stage `n`. -/
theorem stageComparison_fac (I : X.IdealSheafData)
    (F : SequentialInverseSystem X.Modules)
    (h_kernel : ∀ k : ℕ, kernelSubobject (F.stepMap k) =
      imageSubobject (SheafOfModules.RingedSite.IdealSheaf.powerAction I.toSubobject
        (F.obj (op (k + 1))) (k + 1))) (n : ℕ) :
    cokernel.π (SheafOfModules.RingedSite.IdealSheaf.powerAction I.toSubobject
        (limit F : X.Modules) (n + 1)) ≫ stageComparison I F h_kernel n =
      limit.π F (op n) := sorry

variable (I : X.IdealSheafData) (F : SequentialInverseSystem X.Modules)

/-- For a finite-type quasi-coherent ideal and a quasi-coherent ideal-adic quotient
tower, the canonical comparison from `(limit F) / I ^ (n + 1) (limit F)` to stage `n` is an
isomorphism. -/
@[stacks 0EI8]
theorem stageComparison_isIso [I.toModule.IsQuasicoherent]
    [∀ n : ℕ, (F.obj (op n)).IsQuasicoherent]
    [h_epi : ∀ n : ℕ, Epi (F.stepMap n)]
    (h_kernel : ∀ n : ℕ, kernelSubobject (F.stepMap n) =
      imageSubobject (powerAction I.toSubobject (F.obj (op (n + 1))) (n + 1)))
    (hI : I.IsFiniteType) (n : ℕ) :
    IsIso (stageComparison I F h_kernel n) := sorry

/-- For a finite-type quasi-coherent ideal and a quasi-coherent ideal-adic quotient
tower, the canonical comparison from `I ^ (n + 1) (limit F)` to the limit of the fixed-power
tail beginning at stage `n` is an isomorphism. -/
@[stacks 0EI8]
theorem powerLimitComparison_isIso [I.toModule.IsQuasicoherent]
    [∀ n : ℕ, (F.obj (op n)).IsQuasicoherent]
    [h_epi : ∀ n : ℕ, Epi (F.stepMap n)]
    (h_kernel : ∀ n : ℕ, kernelSubobject (F.stepMap n) =
      imageSubobject (powerAction I.toSubobject (F.obj (op (n + 1))) (n + 1)))
    (hI : I.IsFiniteType) (n : ℕ) :
    IsIso (powerLimitComparison I F n) := sorry

end AlgebraicGeometry.Scheme.Modules.AdicLimit

end
