module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ResolutionProperty.Noetherian
import StacksCheckRecall

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

/- Lemma 76.56.2: In Situation 76.56.1, assume `X` is Noetherian. Then for any
coherent `𝒪_X`-module `F` there exist `r ≥ 0`, integers `n₁, …, nᵣ ≥ 0`, and a
surjection `∐ i, (Modules.pushforward π).obj (I.pow (n i)).toModule ⟶ F` of
`𝒪_X`-modules. -/
@[stacks 0GUZ] #check
  (AlgebraicGeometry.AlgebraicSpace.ResolutionDescent.exists_epi_coproduct_pushforward_pow :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsNoetherian X]
      (sit : ResolutionDescent X) (F : X.Modules) [F.IsCoherent],
    ∃ (r : ℕ) (n : Fin r → ℕ)
      (q : (∐ fun i : Fin r ↦
        (Modules.pushforward sit.π).obj (sit.I.pow (n i)).toModule) ⟶ F),
      Epi q)
