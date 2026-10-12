/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Remark_90_12_5_Slice
public import stacks_project.Chap90.Remark_90_12_5_TangentSpace
import StacksCheckRecall

/-!
# Tangent spaces of categories cofibered in groupoids

The tangent space and differential of a predeformation category globalize to an
arbitrary category cofibered in groupoids over `C_Λ` by passing to the residue
slice of Remark 90.6.4.
-/

@[expose] public section

open CategoryTheory ArtinianLocalAlgCat Functor
open scoped Bicategory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G : Type v} [Category.{w} F] [Category.{w} G]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) (q : G ⥤ ArtinianLocalAlgCat Λ k)
variable [IsFibered.InGroupoids p.op] [IsFibered.InGroupoids q.op]
variable (x : p.Fiber (residue Λ k))
variable (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)

/- Remark 90.12.5 (1): Let F be a category cofibered in groupoids over C_Λ, and let
x be an object of F(k). As in Remark 90.6.4, we get a predeformation category F_x.
We define T_x F = T F_x to be the tangent space of F at x. This is
`Functor.tangentSpaceAt`. -/
@[stacks 06IK]
#check Functor.tangentSpaceAt p x

/- Remark 90.12.5 (2): If φ : F ⟶ G is a morphism of categories cofibered in groupoids
over C_Λ and x is an object of F(k), then there is an induced morphism
φ_x : F_x ⟶ G_{φ(x)}. This is `BasedFunctor.sliceMap`. -/
@[stacks 06IK]
#check BasedFunctor.sliceMap φ x

/- Remark 90.12.5 (3): We define the differential d_x φ : T_x F ⟶ T_{φ(x)} G of φ at x
to be the map d φ_x : T F_x ⟶ T G_{φ(x)}. This is `BasedFunctor.differentialAt`. -/
@[stacks 06IK]
#check BasedFunctor.differentialAt φ x

variable [HasSchlessingerS2 p] [HasSchlessingerS2 q]

/- Remark 90.12.5 (4): If both F and G satisfy (S2) then all of these tangent spaces
have a natural k-vector space structure (use Lemmas 90.10.6 and 90.12.4). -/
@[stacks 06IK]
#check (Functor.instModule_tangentSpaceAt p x : Module k (Functor.tangentSpaceAt p x))

/- Remark 90.12.5 (5): If both F and G satisfy (S2) then all the differentials
d_x φ : T_x F ⟶ T_{φ(x)} G are k-linear (use Lemmas 90.10.6 and 90.12.4). -/
@[stacks 06IK]
#check BasedFunctor.isLinearMap_differentialAt φ x
