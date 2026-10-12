/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap75.Definition_75_28_1_ResolutionProperty
public import stacks_project.Chap76.Situation_76_56_1_Descent

/-!
# Resolution property of quasi-compact quasi-separated algebraic spaces

On a quasi-compact quasi-separated algebraic space equipped with affine étale
descent data as in Situation 76.56.1, the resolution property is equivalent to
the pushforward of the chosen ideal being a quotient of a finite locally free
module, with no Noetherian hypothesis.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ResolutionDescent

/-- Lemma 76.56.4: In Situation 76.56.1, the algebraic space `X` has the
resolution property if and only if `(Modules.pushforward sit.π).obj sit.I.toModule`
is a quotient of a finite locally free `𝒪_X`-module. -/
@[stacks 0GV1]
theorem hasResolutionProperty_iff_epi_pushforward_ideal
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (sit : ResolutionDescent X) :
    HasResolutionProperty X ↔
      ∃ (E : X.Modules) (_ : E.IsFiniteLocallyFree)
        (q : E ⟶ (Modules.pushforward sit.π).obj sit.I.toModule),
        Epi q :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ResolutionDescent
