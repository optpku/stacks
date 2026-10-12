/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap69.Definition_69_12_1_Instances
public import stacks_project.Chap71.Definition_71_17_1_Rees
public import stacks_project.Chap76.Situation_76_56_1_Descent

/-!
# Generating coherent modules by pushforwards of ideal powers

On a Noetherian algebraic space equipped with affine étale descent data as in
Situation 76.56.1, every coherent module is a quotient of a finite coproduct of
pushforwards of powers of the chosen ideal.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ResolutionDescent

/-- Lemma 76.56.2: In Situation 76.56.1, assume `X` is Noetherian. Then for any
coherent `𝒪_X`-module `F` there exist `r ≥ 0`, integers `n₁, …, nᵣ ≥ 0`, and a
surjection `∐ i, (Modules.pushforward π).obj (I.pow (n i)).toModule ⟶ F` of
`𝒪_X`-modules. -/
@[stacks 0GUZ]
theorem exists_epi_coproduct_pushforward_pow
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsAbsolutelyQuasiSeparated X] [IsNoetherian X]
    (sit : ResolutionDescent X) (F : X.Modules) [F.IsCoherent] :
    ∃ (r : ℕ) (n : Fin r → ℕ)
      (q : (∐ fun i : Fin r ↦
        (Modules.pushforward sit.π).obj (sit.I.pow (n i)).toModule) ⟶ F),
      Epi q :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ResolutionDescent
