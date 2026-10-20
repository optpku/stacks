module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Devissage
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 30.12.8: let `X` be a nonempty Noetherian scheme and let `P` be an
extension-closed property of coherent `𝒪_X`-modules which descends from nonempty finite
self-coproducts. If `P` admits a generic model on every irreducible closed support, then `P`
holds for every coherent module on `X`. -/
@[stacks 01YM] #check
  (AlgebraicGeometry.Scheme.Modules.devissagePropertyHoldsOfIntegralClosedGenericModels :
    ∀ {X : Scheme.{u}} [Nonempty X] [IsNoetherian X]
      (P : X.Modules → Prop)
      (h_shortExact : AlgebraicGeometry.Scheme.Modules.DevissageShortExactClosed P)
      (h_coproduct :
        AlgebraicGeometry.Scheme.Modules.DevissageDescendsFromFiniteCoproducts P)
      (h_generic :
        ∀ (Z₀ : TopologicalSpace.IrreducibleCloseds X) (ξ : X),
          IsGenericPoint ξ (Z₀ : Set X) →
            AlgebraicGeometry.Scheme.Modules.DevissageGenericModel Z₀ ξ P)
      (ℱ : X.Modules) [ℱ.IsCoherent],
      P ℱ)
