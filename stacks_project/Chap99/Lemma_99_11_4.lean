/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative.ExactSequence
import StacksCheckRecall

/-!
# Split exactness of `0 → Pic(T) → Pic(X_T) → Pic_{X/B}(T) → 0`

If `σ : B ⟶ X` is a section of `f` and `𝒪_T ⟶ (f_T)_* 𝒪_{X_T}` is an
isomorphism for every scheme `T` over `B`, the Picard sequence of Lemma 99.11.3
is split exact, with splitting `σ_T^*`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.CohStack

noncomputable section

universe u

/- Lemma 99.11.4 (1): in Situation 99.11.1, a chosen section and the
structure-sheaf isomorphism after every scheme base change make the canonical
map `Pic(X_T) → Pic_{X/B}(T)` surjective. -/
@[stacks 0D28] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativePicard.picardSequence_surjective :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) (σ : B ⟶ X),
      σ ≫ f = 𝟙 B →
      (∀ τ : SchemesOver B, IsIso (structureSheafMap (fiberToBase f τ))) →
      ∀ τ : SchemesOver B, Function.Surjective (RelativePicard.toFunctor f τ))

/- Lemma 99.11.4 (2): existing exactness supplies both injectivity of
`Pic(T) → Pic(X_T)` and exactness at `Pic(X_T)`. These two clauses require
only the universal structure-sheaf hypothesis, independently of the section. -/
@[stacks 0D28] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativePicard.picardSequence_exact :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S} (f : X ⟶ B),
      (∀ τ : SchemesOver B, IsIso (structureSheafMap (fiberToBase f τ))) →
      ∀ τ : SchemesOver B,
      Function.Injective (picardPullback (fiberToBase f τ)) ∧
        ∀ L : (fiber f τ).PicardGroup,
          RelativePicard.toFunctor f τ L = RelativePicard.toFunctor f τ 0 ↔
            L ∈ Set.range (picardPullback (fiberToBase f τ)))

/- Lemma 99.11.4 (3): pullback along the base-changed section is the stated
splitting `σ_T^*`. This independent left-inverse identity holds without
the universal structure-sheaf hypothesis `h_iso`. -/
@[stacks 0D28] #check
  (AlgebraicGeometry.AlgebraicSpace.RelativePicard.picardSequence_split :
    ∀ {S : Scheme.{u}} {X B : AlgebraicSpace S}
      (f : X ⟶ B) (σ : B ⟶ X) (hσ : σ ≫ f = 𝟙 B) (τ : SchemesOver B),
      Function.LeftInverse (Picard.WithSection.sectionPicard f σ hσ τ)
        (picardPullback (fiberToBase f τ)))
