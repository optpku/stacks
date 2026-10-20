/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Basic

/-!
# Affine-local criteria for locally projective scheme modules

This leaf gives the affine-cover and affine-scheme forms of local projectivity.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- For a quasi-coherent scheme module, local projectivity is equivalent to projectivity of
sections on the members of some affine open cover. -/
@[stacks 05JQ]
theorem isLocallyProjective_iff_exists_affineOpenCover_projectiveSections
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    IsLocallyProjective ℱ ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          Module.Projective (Γ(X, (𝒰.f i).opensRange)) (Γ(ℱ, (𝒰.f i).opensRange)) := sorry

/-- The associated module sheaf `M^~` on `Spec R` is locally projective exactly when the
`R`-module `M` is projective. -/
@[stacks 05JQ]
theorem tilde_isLocallyProjective_iff_module_projective
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    IsLocallyProjective (tilde M) ↔ Module.Projective R M := sorry

/-- The module sheaf associated to a projective module is locally projective. -/
instance instIsLocallyProjectiveTilde
    {R : CommRingCat.{u}} (M : ModuleCat R) [Module.Projective R M] :
    IsLocallyProjective (tilde M) := sorry

end AlgebraicGeometry.Scheme.Modules
