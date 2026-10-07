module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion

open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

universe u

#check (AlgebraicGeometry.Scheme.Modules.SectionTorsion.Is :
  ∀ {X : Scheme.{u}} [IsIntegral X] (ℱ : X.Modules) {U : X.Opens},
    ℱ.val.obj (op U) → Prop)

/- Definition 31.11.2: Let `X` be an integral scheme and let `ℱ` be a quasicoherent
`𝒪_X`-module. A local section is torsion when its germ is torsion at every point, and `ℱ` is
torsion free exactly when every torsion local section is zero. -/
@[stacks 0AVR] #check
  (AlgebraicGeometry.Scheme.Modules.isTorsionFree_iff_forall_isTorsion_eq_zero :
    ∀ {X : Scheme.{u}} [IsIntegral X] (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      AlgebraicGeometry.Scheme.Modules.IsTorsionFree ℱ ↔
        ∀ ⦃U : X.Opens⦄ (s : ℱ.val.obj (op U)),
          AlgebraicGeometry.Scheme.Modules.SectionTorsion.Is ℱ s → s = 0)
