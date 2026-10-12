/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Lemma 28.19.1 compatibility entry point

The affine flatness criterion for associated module sheaves is owned by
`ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine`.
-/

/-
Lemma 28.19.1

For a commutative ring `R` and an `R`-module `M`, the associated module sheaf
`AlgebraicGeometry.tilde M` on `AlgebraicGeometry.Spec R` is flat if and only if
`M` is flat over `R`.
-/
@[stacks 05P0] #check
  (AlgebraicGeometry.Scheme.Modules.tilde_isFlat_iff_module_flat :
    ∀ {R : CommRingCat.{u}} (M : ModuleCat R),
      SheafOfModules.IsFlat (X := (AlgebraicGeometry.Spec R).toRingedSpace)
        (AlgebraicGeometry.tilde M) ↔ Module.Flat R M)
