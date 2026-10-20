module

public import stacks_project.Chap90.Lemma_90_19_7_Comparison
public import stacks_project.Chap90.Lemma_90_19_7_TangentSpace
import StacksCheckRecall

/-!
# Lemma 90.19.7

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and satisfies (RS),
then for `x : F` the identity-tangent space `T_id Aut(x)` carries a natural
`k`-vector space structure whose addition agrees with composition, and there is a
canonical `k`-linear isomorphism with `T_id Aut(x0)` for any specified residue-field pushforward `x0` of `x`.
-/

@[expose] public section

open CategoryTheory hiding Linear
open CategoryTheory.Functor
open ArtinianLocalAlgCat

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

open CategoryTheory.Functor.Fiber

/- Lemma 90.19.7 (1): Let `F` be a category cofibered in groupoids over `C_Λ`
satisfying (RS). Let `x` be an object of `F(A)`. Then `T_id Aut(x)` has a natural
`k`-vector space structure such that addition agrees with composition in
`T_id Aut(x)`. In particular, composition in `T_id Aut(x)` is commutative. -/
@[stacks 06JV] #check (CategoryTheory.Functor.idTangentSpace_add_eq_mul :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x), α + β = α * β)

#check (CategoryTheory.Functor.idTangentSpace_mul_comm :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p] {x : F}
    (α β : idTangentSpace p x), α * β = β * α)

/- Lemma 90.19.7 (2): Every specified pushforward `x0` of `x` to the residue fibre
induces a canonical `k`-linear isomorphism of identity-tangent spaces. -/
@[stacks 06JV] #check (CategoryTheory.Functor.idTangentSpaceLinearEquivOfPushforward :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x : F) (x0 : p.Fiber (residue Λ k)) (φ : x ⟶ fiberInclusion.obj x0)
    [p.IsStronglyCocartesian (toResidue (p.obj x)) φ],
    idTangentSpace p x ≃ₗ[k] idTangentSpace p (fiberInclusion.obj x0))
