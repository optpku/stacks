module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.TangentCriterion
import StacksCheckRecall

/-!
# Characterization of normalized and minimal groupoids in functors

A smooth prorepresentable groupoid in functors on `C_Λ` is normalized if and only if
`U ⟶ [U/R]` induces a bijection on tangent spaces, and it is minimal if and only if
the kernel of `TU → T[U/R]` is contained in the image of `Derivation Λ k k → TU`.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat
open Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.GroupoidInFunctors

/- Lemma 90.27.2 (1): a smooth prorepresentable groupoid in functors `(U, R, s, t, c)`
on `ArtinianLocalAlgCat Λ k` is normalized if and only if the morphism `U ⟶ [U/R]`
induces a bijection `TU → T[U/R]` on tangent spaces. -/
@[stacks 06KN]
#check (CategoryTheory.GroupoidInFunctors.isNormalized_iff_bijective_quotientTangentSpaceMap :
  ∀ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G],
    IsNormalized G ↔ Function.Bijective (quotientTangentSpaceMap G))

/- Lemma 90.27.2 (2): a smooth prorepresentable groupoid in functors `(U, R, s, t, c)`
on `ArtinianLocalAlgCat Λ k` is minimal if and only if the kernel of
`TU → T[U/R]` is contained in the image of `Derivation Λ k k → TU`. -/
@[stacks 06KN]
#check (CategoryTheory.GroupoidInFunctors.isMinimal_iff_ker_quotientTangentSpaceMap_le_range_ofDerivation :
  ∀ (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
    [IsSmooth G.s G.t] [IsProrepresentable G],
    IsMinimal G ↔
      ∀ (x0 : G.U.obj (residue Λ k)) (x : G.U.obj (dualNumber Λ k)),
        quotientTangentSpaceMap G x =
          quotientTangentSpaceMap G (G.U.map (residueToDualNumber Λ k) x0) →
        x ∈ Set.range (fun D : Derivation Λ k k ↦
          G.U.map (derivationToDualNumber D) x0))

end CategoryTheory.GroupoidInFunctors
