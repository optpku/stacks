module

public import ReasLib.AlgebraicGeometry.FormalDeformation.CompleteLocal.Derivation
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.ProrepresentableTangent
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

/- Example 90.11.11 (1): for a finite-dimensional `k`-vector space `V`,
`F(k[V]) = Mor_{C_Λ}(S, k[V]) = Der_Λ(S, V)`, via `D s = f s - q s` and
`f s = q s + D s`. -/
@[stacks 06IC] #check (CompleteLocalAlgCat.homEquivDerivation :
  ∀ (S : CompleteLocalAlgCat Λ k) (V : Type u) [AddCommGroup V] [Module k V]
    [Module Λ V] [IsScalarTower Λ k V] [Module.Finite k V],
    (S ⟶ ArtinianLocalAlgCat.inclusion.obj (ArtinianLocalAlgCat.squareZero Λ k V)) ≃
      Derivation Λ S.carrier V)

/- Example 90.11.11 (2): `TF = F(k[ε]) = Mor_{C_Λ}(S, k[ε]) = Der_Λ(S, k)`,
and the identifications are `k`-linear. -/
@[stacks 06IC] #check
  (CategoryTheory.Functor.IsPredeformationFunctor.tangentSpaceLinearEquivDerivation :
    ∀ (S : CompleteLocalAlgCat Λ k),
      tangentSpace (restrictedCoyoneda S) ≃ₗ[k] Derivation Λ S.carrier k)

/- Example 90.11.11 (3): `dim_k TF` is finite by Lemma 90.4.5, since `TF`
identifies with `Derivation Λ S.carrier k`. -/
@[stacks 06IC] #check
  (CategoryTheory.Functor.IsPredeformationFunctor.finiteDimensional_tangentSpace_restrictedCoyoneda :
    ∀ (S : CompleteLocalAlgCat Λ k),
      FiniteDimensional k (tangentSpace (restrictedCoyoneda S)))
