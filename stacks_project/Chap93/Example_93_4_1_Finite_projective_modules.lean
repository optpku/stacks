/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FiniteProjective
public import ReasLib.AlgebraicGeometry.FormalDeformation.FiniteProjective.Deformation
import StacksCheckRecall

/-!
# Finite projective modules as a category cofibered in groupoids
-/

@[expose] public section

open CategoryTheory

universe u

/- Example 93.4.1 (Finite projective modules) (1): the category `F` of pairs `(A, M)` with
`M` a finite projective `A`-module, with morphisms `(f, g) : (B, N) ⟶ (A, M)` given by
`f : B ⟶ A` in `C_Λ` together with an `f`-linear map inducing `N ⊗_{B, f} A ≅ M`,
and with projection `p : F ⥤ C_Λ` cofibered in groupoids. -/
@[stacks 0D3I]
#check
  (ArtinianLocalAlgCat.FiniteProjective.groupoids :
    ∀ (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k],
      CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
        (ArtinianLocalAlgCat Λ k))

#check
  (ArtinianLocalAlgCat.FiniteProjective.instInGroupoids_forget :
    ∀ (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k],
      Functor.IsFibered.InGroupoids
        (Pseudofunctor.Grothendieck.forget
          (ArtinianLocalAlgCat.FiniteProjective.pseudofunctor Λ k)).op)

/- Example 93.4.1 (Finite projective modules) (2): given a finite-dimensional `k`-vector
space `V`, the object `x₀ = (k, V)` of `F(k)` and the slice `Def_V = F_{x₀}`. -/
@[stacks 0D3I]
#check
  (ArtinianLocalAlgCat.FiniteProjective.deformation :
    ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
      [Module.Finite Λ k] (V : Type u) [AddCommGroup V] [Module k V]
      [FiniteDimensional k V],
      CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u}
        (ArtinianLocalAlgCat Λ k))
