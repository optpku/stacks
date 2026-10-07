module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Subobject

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped AlgebraicGeometry

universe u

/- Lemma 31.11.4: Let `X` be an integral scheme and let `ℱ` be a quasicoherent
`𝒪_X`-module. The torsion sections of `ℱ` form a quasicoherent `𝒪_X`-submodule, and the
quotient by this submodule is torsion free. -/
@[stacks 0AXT] #check
  (AlgebraicGeometry.Scheme.Modules.torsionSubobject_spec :
    ∀ {X : Scheme.{u}} [IsIntegral X]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      (∀ (U : X.Opens) (s : Γ(ℱ, U)),
          s ∈ SheafOfModules.Subobject.sections
            (AlgebraicGeometry.Scheme.Modules.torsionSubobject ℱ) (op U) ↔
            AlgebraicGeometry.Scheme.Modules.SectionTorsion.Is ℱ s) ∧
        ((AlgebraicGeometry.Scheme.Modules.torsionSubobject ℱ :
          X.Modules)).IsQuasicoherent ∧
        AlgebraicGeometry.Scheme.Modules.IsTorsionFree
          (cokernel (AlgebraicGeometry.Scheme.Modules.torsionSubobject ℱ).arrow))
