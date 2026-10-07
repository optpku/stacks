module

public import stacks_project.Chap90.Definition_90_11_9_TangentSpace
public import stacks_project.Chap90.Lemma_90_11_6
public import stacks_project.Chap90.Lemma_90_11_8
public import stacks_project.Chap90.Lemma_90_11_13

/-!
# Lemma 90.11.15

Under the hypotheses of Lemma 90.11.8, with `R = K` a field, the canonical
comparison `TF ⊗[K] V → F(K[V])` is bijective for every finite-dimensional
`K`-vector space `V`.
-/

@[expose] public section

noncomputable section

open CategoryTheory hiding Linear
open TrivSqZeroExt
open FGModuleCat
open scoped TensorProduct

universe u

namespace CategoryTheory.Functor

variable {S K : Type u} [CommRing S] [Field K] [Algebra S K]
variable {P : ObjectProperty (Over (CommAlgCat.of S K))}
variable [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
variable {F : P.FullSubcategory ⥤ Type u}
variable [Unique (F.obj (overSelfObj P))] [F.BijectiveOnFGSquareZeroProds]

/-- The additive group structure of Lemma 90.11.8 on the tangent space `TF`. -/
instance instAddCommGroup_tangentSpace : AddCommGroup (tangentSpace F) :=
  instAddCommGroup (fgEval P F) (of K K)

/-- The `K`-module structure of Lemma 90.11.8 on the tangent space `TF`. -/
instance instModule_tangentSpace : Module K (tangentSpace F) :=
  instModule (fgEval P F) (of K K)

variable (F) (V : FGModuleCat.{u} K)

/-- The canonical `K`-linear comparison `TF ⊗[K] V →ₗ[K] F(K[V])`, sending
`x ⊗ₜ v` to the image of `x` under the map induced by `spanSingleton v`. -/
def tangentSpaceTensor : tangentSpace F ⊗[K] V →ₗ[K] F.obj ((fgLift P).obj V) :=
  TensorProduct.lift (tensorBilin (linearLift (fgEval P F)) V)

/-- `tangentSpaceTensor` is the underlying `K`-linear map of
`(tensorNatTrans (linearLift (fgEval P F))).app V`. -/
theorem tangentSpaceTensor_spec :
    ModuleCat.ofHom (tangentSpaceTensor F V) =
      (tensorNatTrans (linearLift (fgEval P F))).app V := sorry

/-- On pure tensors, `tangentSpaceTensor F V` sends `x ⊗ₜ v` to
`(linearLift (fgEval P F)).map (spanSingleton v) x`. -/
theorem tangentSpaceTensor_tmul (x : tangentSpace F) (v : V) :
    tangentSpaceTensor F V (x ⊗ₜ v) =
      (linearLift (fgEval P F) : FGModuleCat.{u} K ⥤ ModuleCat.{u} K).map (spanSingleton v) x := sorry

/-- Lemma 90.11.15: Let `F : C ⥤ Type` be a functor satisfying the hypotheses of
Lemma 90.11.8. Assume `R = K` is a field. Then `F(K[V]) ≅ TF ⊗[K] V` for any
finite-dimensional `K`-vector space `V`, via the canonical comparison
`tangentSpaceTensor F V : TF ⊗[K] V →ₗ[K] F(K[V])`. -/
@[stacks 06IE]
theorem bijective_tangentSpaceTensor :
    Function.Bijective (tangentSpaceTensor F V) := sorry

end CategoryTheory.Functor
