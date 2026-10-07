module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Depth

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

/- Lemma 31.11.13: let `X` be an integral locally Noetherian scheme. Let
`φ : ℱ ⟶ 𝒢` be a map of quasi-coherent `𝒪_X`-modules. Assume `ℱ` is coherent, `𝒢` is torsion
free, and that for every point `x : X` either the stalk map of `φ` at `x` is an isomorphism or
the stalk of `ℱ` at `x` has depth at least two. Then `φ` is an isomorphism. -/
@[stacks 0AVS] #check (
  AlgebraicGeometry.Scheme.Modules.isIso_of_stalkwise_or_depth_of_isTorsionFree :
    ∀ {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
      {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsQuasicoherent]
      [AlgebraicGeometry.Scheme.Modules.IsTorsionFree 𝒢]
      (φ : ℱ ⟶ 𝒢),
      (∀ x : X,
        IsIso (moduleStalkHom x φ) ∨
          (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (stalkModuleCat ℱ x)) →
        IsIso φ)
