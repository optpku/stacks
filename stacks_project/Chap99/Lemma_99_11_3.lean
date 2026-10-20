module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative.ExactSequence
import StacksCheckRecall

/-!
# Exactness of `0 → Pic(T) → Pic(X_T) → Pic_{X/B}(T)`

If `𝒪_T ⟶ (f_T)_* 𝒪_{X_T}` is an isomorphism for every scheme `T` over `B`,
the sheafification unit of `T ↦ Pic(X_T)` is left exact on Picard groups.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
universe u

/- Lemma 99.11.3: in Situation 99.11.1, if `𝒪_T ⟶ (f_T)_* 𝒪_{X_T}` is an
isomorphism for every scheme `T` over `B`, then
`0 → Pic(T) → Pic(X_T) → Pic_{X/B}(T)` is exact for every such `T`. -/
@[stacks 0D27] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativePicard.picardSequence_exact :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B)
    (h_iso : ∀ σ : SchemesOver B, IsIso (structureSheafMap (fiberToBase f σ)))
    (σ : SchemesOver B),
    Function.Injective (picardPullback (fiberToBase f σ)) ∧
      ∀ L : (fiber f σ).PicardGroup,
        RelativePicard.toFunctor f σ L = RelativePicard.toFunctor f σ 0 ↔
          L ∈ Set.range (picardPullback (fiberToBase f σ)))

