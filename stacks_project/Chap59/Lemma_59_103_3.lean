/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_103_3_Comparison
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.HComparison
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HComparison

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasSheafify X.smallEtaleTopology (Type (u + 1))]
variable [HasSheafify Y.smallEtaleTopology (Type (u + 1))]

/-- Lemma 59.103.3: in the setting of Lemma 59.103.2, if `f : X ⟶ Y` is a proper
morphism of schemes, the canonical mate `a_Y⁻¹ ∘ f_small,* ⟶ f_big,h,* ∘ a_X⁻¹`
is an isomorphism of functors on sheaves of sets, where `a_X = π_X ∘ ε_X` is the
composite comparison from the small étale topos of `X` to the big h topos of `X`.
A morphism of `(Sch/S)_h` is used via its underlying scheme morphism. -/
@[stacks 0EWA]
theorem proper_smallHPushforward_isIso [IsProper f] :
    IsIso (smallHPushforwardHom f) := sorry

end AlgebraicGeometry.Scheme.HComparison

end

end
