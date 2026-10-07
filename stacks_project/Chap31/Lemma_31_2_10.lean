module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Injectivity
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 31.2.10: let `X` be a locally Noetherian scheme and let `φ : ℱ ⟶ 𝒢` be a morphism of
quasicoherent `𝒪_X`-modules. If, for every point `x : X`, either the stalk map of `φ` at `x` is
injective or `x` is not an associated point of `ℱ`, then `φ` is a monomorphism. -/
@[stacks 0AVL] #check
  (AlgebraicGeometry.Scheme.Modules.mono_of_stalkwise_injective_or_not_mem_associatedPoints :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]
      (φ : ℱ ⟶ 𝒢),
      (∀ x : X,
        Function.Injective (AlgebraicGeometry.RingedSpace.moduleStalkHom x φ) ∨
          x ∉ AlgebraicGeometry.Scheme.Modules.associatedPoints ℱ) →
        Mono φ)
