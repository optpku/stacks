module

public import stacks_project.Chap90.Example_90_11_11_Derivation
public import stacks_project.Chap90.Lemma_90_4_5
import StacksCheckRecall

/-!
# Tangent space of a prorepresentable functor

For `F = underline{S}|_{C_Λ}`, morphisms into `k[V]` are `Λ`-derivations into `V`,
and the tangent space `TF = F(k[ε])` is finite-dimensional over `k`.
-/

@[expose] public section

open CategoryTheory
open CompleteLocalAlgCat
open Functor.IsPredeformationFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable (S : CompleteLocalAlgCat Λ k)

/- Example 90.11.11 (1): for a finite-dimensional `k`-vector space `V`,
`F(k[V]) = Mor_{C_Λ}(S, k[V]) = Der_Λ(S, V)`, via `D s = f s - q s` and
`f s = q s + D s`. -/
@[stacks 06IC] #check homEquivDerivation

/- Example 90.11.11 (2): `TF = F(k[ε]) = Mor_{C_Λ}(S, k[ε]) = Der_Λ(S, k)`,
and the identifications are `k`-linear. -/
@[stacks 06IC] #check tangentSpaceEquivDerivation

namespace CategoryTheory.Functor.IsPredeformationFunctor

/-- Example 90.11.11 (3): `dim_k TF` is finite by Lemma 90.4.5, since `TF`
identifies with `Derivation Λ S.carrier k`. -/
@[stacks 06IC, instance]
instance finiteDimensional_tangentSpace_restrictedCoyoneda :
    FiniteDimensional k (tangentSpace (restrictedCoyoneda S)) := sorry

end CategoryTheory.Functor.IsPredeformationFunctor
