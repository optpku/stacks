module

public import stacks_project.Chap93.Example_93_4_1_Finite_projective_modules_Groupoids
public import stacks_project.Chap93.Example_93_4_1_Finite_projective_modules_Slice
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
#check ArtinianLocalAlgCat.FiniteProjective.groupoids

@[stacks 0D3I]
#check fun {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] ↦
  (inferInstance :
    Functor.IsFibered.InGroupoids
      (ArtinianLocalAlgCat.FiniteProjective.groupoids Λ k).p.op)

/- Example 93.4.1 (Finite projective modules) (2): given a finite-dimensional `k`-vector
space `V`, the object `x₀ = (k, V)` of `F(k)` and the slice `Def_V = F_{x₀}`. -/
@[stacks 0D3I]
#check ArtinianLocalAlgCat.FiniteProjective.deformation
