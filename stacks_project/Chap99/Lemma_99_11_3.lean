/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import stacks_project.Chap99.Situation_99_11_1

/-!
# Exactness of `0 → Pic(T) → Pic(X_T) → Pic_{X/B}(T)`

If `𝒪_T ⟶ (f_T)_* 𝒪_{X_T}` is an isomorphism for every scheme `T` over `B`,
the sheafification unit of `T ↦ Pic(X_T)` is left exact on Picard groups.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.AlgebraicSpace.CohStack
open AlgebraicGeometry.AlgebraicSpace.PreRelation (schemesOverFppf)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The canonical map `Pic(X_T) ⟶ Pic_{X/B}(T)` given by the sheafification unit
of the relative Picard presheaf at a scheme `T` over `B`. -/
def toFunctor (f : X ⟶ B) (σ : SchemesOver B) :
    (fiber f σ).PicardGroup → (functor f).obj.obj (op σ) :=
  ((sheafificationAdjunction (schemesOverFppf B) (Type (u + 1))).unit.app
      (presheaf f)).app (op σ)

/-- Unfolding: `toFunctor f σ` is the component of the sheafification unit of
`presheaf f` at `σ`. -/
theorem toFunctor_apply (f : X ⟶ B) (σ : SchemesOver B)
    (L : (fiber f σ).PicardGroup) :
    toFunctor f σ L =
      ((sheafificationAdjunction (schemesOverFppf B) (Type (u + 1))).unit.app
          (presheaf f)).app (op σ) L :=
  sorry

/-- Lemma 99.11.3: in Situation 99.11.1, if `𝒪_T ⟶ (f_T)_* 𝒪_{X_T}` is an
isomorphism for every scheme `T` over `B`, then
`0 → Pic(T) → Pic(X_T) → Pic_{X/B}(T)` is exact for every such `T`. -/
@[stacks 0D27]
theorem picardSequence_exact (f : X ⟶ B)
    (h_iso : ∀ σ : SchemesOver B, IsIso (structureSheafMap (fiberToBase f σ)))
    (σ : SchemesOver B) :
    Function.Injective (picardPullback (fiberToBase f σ)) ∧
      ∀ L : (fiber f σ).PicardGroup,
        toFunctor f σ L = toFunctor f σ 0 ↔
          L ∈ Set.range (picardPullback (fiberToBase f σ)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
