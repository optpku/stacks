/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Affine

/-!
# Pullback of locally projective scheme modules

Local projectivity of quasi-coherent scheme modules is preserved by pullback.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

namespace IsLocallyProjective

/-- Pullback along a morphism of schemes preserves local projectivity of quasi-coherent
scheme modules. -/
@[stacks 060M]
theorem pullback
    (f : X ⟶ Y) {𝒢 : Y.Modules} [𝒢.IsQuasicoherent]
    (h𝒢 : IsLocallyProjective 𝒢) :
    IsLocallyProjective ((Scheme.Modules.pullback f).obj 𝒢) := sorry

end IsLocallyProjective

/-- Pullback along a morphism of schemes preserves local projectivity of quasi-coherent modules. -/
instance instIsLocallyProjectivePullback
    (f : X ⟶ Y) (𝒢 : Y.Modules) [𝒢.IsQuasicoherent] [IsLocallyProjective 𝒢] :
    IsLocallyProjective ((Scheme.Modules.pullback f).obj 𝒢) := sorry

end AlgebraicGeometry.Scheme.Modules
