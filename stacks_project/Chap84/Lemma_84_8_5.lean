/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap84.Lemma_84_8_5_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 84.8.5

In the topos square of Lemma 84.8.4, a proper morphism of algebraic spaces
identifies `a_Y⁻¹ ∘ f_small,*` with `f_big,ph,* ∘ a_X⁻¹` on sheaves of sets, and
identifies `a_Y⁻¹(R f_small,* K)` with `R f_big,ph,* (a_X⁻¹ K)` for `K` in
`D⁺(X_étale)` with torsion cohomology sheaves. Here `a_X = π_X ∘ ε_X` and
`a_Y = π_Y ∘ ε_Y`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.PhComparison
open CategoryTheory CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PhComparison

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Lemma 84.8.5 (1): in the commuting topos square of Lemma 84.8.4, if `f : X ⟶ Y`
is a proper morphism of algebraic spaces over a scheme `S`, then the canonical
mate `smallPhPushforwardHom f` from
`(smallEtaleMorphismOfTopoi f).pushforward ⋙ (toSmallEtale Y)⁻¹` to
`(toSmallEtale X)⁻¹ ⋙ (Ph.Big.morphismOfTopoi f).pushforward` is an isomorphism
of functors on sheaves of sets. Here `toSmallEtale Z` is the composite
`a_Z = π_Z ∘ ε_Z`, so the mate is the comparison
`a_Y⁻¹ ∘ f_small,* ⟶ f_big,ph,* ∘ a_X⁻¹`. -/
@[stacks 0DGX]
theorem proper_smallPhPushforward_isIso [Proper f] :
    IsIso (smallPhPushforwardHom f) := sorry

/-- Objectwise form of `proper_smallPhPushforward_isIso`. -/
theorem proper_smallPhPushforward_app_isIso [Proper f]
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    IsIso ((smallPhPushforwardHom f).app F) := sorry

/-- Lemma 84.8.5 (2): in the commuting topos square of Lemma 84.8.4, if `f : X ⟶ Y`
is a proper morphism of algebraic spaces over a scheme `S` and `K` lies in
`D⁺(X_étale)` with torsion cohomology sheaves, then the canonical mate
`a_Y⁻¹(R f_small,* K) ⟶ R f_big,ph,* (a_X⁻¹ K)` is an isomorphism. Here
`a_X = π_X ∘ ε_X` and `a_Y = π_Y ∘ ε_Y`. -/
@[stacks 0DGX]
theorem proper_plusSmallPhPushforward_isIso [Proper f]
    (K : DerivedCategory.Plus (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}))
    (hK : DerivedCategory.Plus.cohomologyIn
      (Sheaf.torsion (smallEtaleTopology X)) K) :
    IsIso ((plusSmallPhPushforwardHom f).app K) := sorry

end AlgebraicGeometry.AlgebraicSpace.PhComparison

end

end
