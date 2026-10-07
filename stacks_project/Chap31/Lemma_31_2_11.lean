module

import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Depth
import StacksCheckRecall

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open CategoryTheory
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

/- Lemma 31.2.11: let `X` be a locally Noetherian scheme, let `ℱ` and `𝒢` be
`𝒪_X`-modules with `ℱ` coherent and `𝒢` quasi-coherent, and let `φ : ℱ ⟶ 𝒢`.
If at every point the stalk map is an isomorphism, or the source stalk has depth at least two
and the point is not associated to `𝒢`, then `φ` is an isomorphism. -/
@[stacks 0AVM] #check (
  AlgebraicGeometry.Scheme.Modules.isIso_of_stalkwise_or_depth :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsQuasicoherent]
      (φ : ℱ ⟶ 𝒢),
      (∀ x : X,
        IsIso (moduleStalkHom x φ) ∨
          ((2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (stalkModuleCat ℱ x) ∧
            x ∉ AlgebraicGeometry.Scheme.Modules.associatedPoints 𝒢)) →
        IsIso φ)
