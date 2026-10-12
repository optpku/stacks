/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Determinant
public import ReasLib.Algebra.Category.ModuleCat.TensorProduct
public import ReasLib.LinearAlgebra.ExteriorAlgebra.Determinant.Prod
import Mathlib.Tactic.CrossRefAttribute

/-!
# Determinants of binary products in `ModuleCat`

This file bundles the explicit determinant product map for arbitrary module objects.  Its data is
the ambient exterior direct-sum map lifted through the determinant submodule; finite projectivity
is required only to assert that the resulting morphism is an isomorphism.
@stack 0FJB
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct Module.Determinant

universe u v w

namespace ModuleCat.Determinant

variable (R : Type u) [CommRing R]

/-- The canonical determinant product morphism for arbitrary module objects. -/
@[stacks 0FJB "determinant product morphism in ModuleCat"]
def prodHom (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) :
    ModuleCat.TensorProduct.obj R (obj R M) (obj R N) ⟶
      obj R (ModuleCat.of R (M × N)) :=
  ModuleCat.ofHom (Module.Determinant.prodMap R M N)

/-- The underlying linear map of the determinant product morphism is the algebraic determinant
product map. -/
@[simp]
theorem prodHom_hom (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) :
    (prodHom R M N).hom = Module.Determinant.prodMap R M N := sorry

/-- On a pure tensor, the bundled determinant product morphism is the algebraic determinant
product map. -/
@[simp]
theorem prodHom_tmul (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (x : det[R](M)) (y : det[R](N)) :
    prodHom R M N (x ⊗ₜ[R] y) =
      Module.Determinant.prodMap R M N (x ⊗ₜ[R] y) := sorry

/-- After the determinant inclusion, the product morphism is the ambient exterior direct-sum
map. -/
@[reassoc, stacks 0FJB "ambient formula for the determinant product morphism"]
theorem prodHom_ι (M : ModuleCat.{v} R) (N : ModuleCat.{w} R) :
    prodHom R M N ≫ ι R (ModuleCat.of R (M × N)) =
      ModuleCat.ofHom (Module.Determinant.prodAmbientMap R M N) := sorry

/-- After inclusion in the exterior algebra, a pure determinant tensor is the wedge product of
the images under the two canonical product inclusions. -/
@[simp, stacks 0FJB "pure tensor formula for the determinant product morphism"]
theorem ι_prodHom_tmul (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    (x : det[R](M)) (y : det[R](N)) :
    ι R (ModuleCat.of R (M × N)) (prodHom R M N (x ⊗ₜ[R] y)) =
      ExteriorAlgebra.map (LinearMap.inl R M N) (x : ExteriorAlgebra R M) *
        ExteriorAlgebra.map (LinearMap.inr R M N) (y : ExteriorAlgebra R N) := sorry

/-- The determinant product morphism is natural in an ordered pair of module-object
isomorphisms. -/
@[reassoc, stacks 0FJB "naturality of the determinant product morphism"]
theorem prodHom_naturality
    {M M' : ModuleCat.{v} R} {N N' : ModuleCat.{w} R}
    (e : M ≅ M') (f : N ≅ N') :
    ModuleCat.TensorProduct.map R (mapIso R e).hom (mapIso R f).hom ≫
        prodHom R M' N' =
      prodHom R M N ≫
        (mapIso R (e.toLinearEquiv.prodCongr f.toLinearEquiv).toModuleIso).hom := sorry

/-- The canonical determinant product morphism is an isomorphism for finite projective module
objects.  This declaration records only the property; inverse data must not be built from this
placeholder proof. -/
@[stacks 0FJB "determinant product morphism is an isomorphism"]
instance prodHom_isIso (M : ModuleCat.{v} R) (N : ModuleCat.{w} R)
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] :
    IsIso (prodHom R M N) := sorry

end ModuleCat.Determinant
