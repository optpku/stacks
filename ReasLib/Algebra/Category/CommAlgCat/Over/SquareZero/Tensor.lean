/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.Over.SquareZero.TangentSpace
public import ReasLib.Algebra.Category.FGModuleCat.Tensor

/-!
# Tensor comparison for square-zero evaluations

Over a field, the value of a set-valued functor on a finite-dimensional
square-zero extension is canonically the tensor product of its tangent space
with the defining vector space.
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

/-- The tangent space inherits the additive group structure of the
finite-product-preserving square-zero evaluation functor. -/
instance instAddCommGroup_tangentSpace : AddCommGroup (tangentSpace F) :=
  instAddCommGroup (fgEval P F) (of K K)

/-- The tangent space inherits the `K`-module structure of the
finite-product-preserving square-zero evaluation functor. -/
instance instModule_tangentSpace : Module K (tangentSpace F) :=
  instModule (fgEval P F) (of K K)

variable (F) (V : FGModuleCat.{u} K)

/-- The canonical `K`-linear comparison `TF ⊗[K] V →ₗ[K] F(K[V])`, sending
`x ⊗ₜ v` to the image of `x` under the map induced by `spanSingleton v`. -/
def tangentSpaceTensor : tangentSpace F ⊗[K] V →ₗ[K] (fgEval P F).obj V :=
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

/-- For a functor on a strictly full subcategory containing all finitely
generated square-zero extensions over a field `K`, singleton evaluation at
`K` and bijective square-zero product comparisons make the canonical map
`TF ⊗[K] V → F(K[V])` bijective for every finite-dimensional `K`-vector space. -/
theorem bijective_tangentSpaceTensor :
    Function.Bijective (tangentSpaceTensor F V) := sorry

end CategoryTheory.Functor
