/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_102_3_Comparison
public import stacks_project.Chap59.Lemma_59_102_3_Morphism
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.PhComparison
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PhComparison

section
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [HasSheafify X.smallEtaleTopology (Type (u + 1))]
variable [HasSheafify Y.smallEtaleTopology (Type (u + 1))]

/-- Lemma 59.102.3: in the commuting topos square of Lemma 59.102.2, if `f : X ⟶ Y` is
proper, then the canonical mate `smallPhPushforwardHom f` from
`(smallMorphism f).pushforward ⋙ (toSmallEtale Y)⁻¹` to
`(toSmallEtale X)⁻¹ ⋙ (Ph.Big.morphismOfTopoi f).pushforward` is an isomorphism
of functors on sheaves of sets. Here `toSmallEtale S` is the composite
`a_S = π_S ∘ ε_S` of `siteMorphismOfTopoi S` with `standardComparison .etale S`,
so the mate is the comparison `a_Y⁻¹ ∘ f_small,* ⟶ f_big,ph,* ∘ a_X⁻¹`. -/
@[stacks 0DDY]
theorem proper_smallPhPushforward_isIso [IsProper f] :
    IsIso (smallPhPushforwardHom f) := sorry

/-- Objectwise form of `proper_smallPhPushforward_isIso`. -/
theorem proper_smallPhPushforward_app_isIso [IsProper f]
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    IsIso ((smallPhPushforwardHom f).app F) := sorry

end

/-- Specialization of `proper_smallPhPushforward_isIso` to a morphism of schemes over a base. -/
theorem proper_smallPhPushforward_isIso_over {S : Scheme.{u}} {X Y : Over S}
    (f : X ⟶ Y) [IsProper f.left]
    [HasSheafify X.left.smallEtaleTopology (Type (u + 1))]
    [HasSheafify Y.left.smallEtaleTopology (Type (u + 1))] :
    IsIso (smallPhPushforwardHom f.left) := sorry

end AlgebraicGeometry.Scheme.PhComparison

end

end
