module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.TensorPower

/-!
# Integral tensor-power twists of quasicoherent modules

This file lifts tensoring by integral powers of an invertible scheme module to the
category of quasicoherent modules.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

variable {X : Scheme.{u}}

/-- Twisting a quasicoherent module by an integral power of an invertible module remains
quasicoherent. -/
theorem twistByTensorPower_isQuasicoherent
    (L : X.Modules) [Modules.Invertible L] (F : X.QCoh) (n : ℤ) :
    (Modules.twistByTensorPower L F.obj n).IsQuasicoherent := sorry

/-- The tensor-power twist, formed in the category of quasicoherent modules. -/
noncomputable def twistByTensorPower
    (L : X.Modules) [Modules.Invertible L] (F : X.QCoh) (n : ℤ) : X.QCoh :=
  ⟨Modules.twistByTensorPower L F.obj n,
    twistByTensorPower_isQuasicoherent L F n⟩

/-- Forgetting quasicoherence identifies the quasicoherent twist with the underlying module
twist. -/
theorem twistByTensorPower_obj
    (L : X.Modules) [Modules.Invertible L] (F : X.QCoh) (n : ℤ) :
    (twistByTensorPower L F n).obj = Modules.twistByTensorPower L F.obj n := sorry

end AlgebraicGeometry.Scheme.QCoh
