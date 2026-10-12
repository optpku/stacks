/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.TorsionFree
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 31.12.4 (1): a coherent reflexive module on an integral locally Noetherian scheme is
torsion-free. -/
@[stacks 0AY2] #check
  (@AlgebraicGeometry.Scheme.Modules.IsReflexive.to_isTorsionFree :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X]
      (ℱ : X.Modules) [SheafOfModules.IsCoherent ℱ]
      [AlgebraicGeometry.Scheme.Modules.IsReflexive ℱ],
      AlgebraicGeometry.Scheme.Modules.IsTorsionFree ℱ)

/- Lemma 31.12.4 (2): for a coherent module on an integral locally Noetherian scheme, the
canonical map to its double dual is a monomorphism exactly when the module is torsion-free. -/
@[stacks 0AY2] #check
  (@AlgebraicGeometry.Scheme.Modules.mono_toReflexiveHull_iff_isTorsionFree :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
      [AlgebraicGeometry.IsLocallyNoetherian X]
      (ℱ : X.Modules) [SheafOfModules.IsCoherent ℱ],
      CategoryTheory.Mono (AlgebraicGeometry.Scheme.Modules.toReflexiveHull ℱ) ↔
        AlgebraicGeometry.Scheme.Modules.IsTorsionFree ℱ)
