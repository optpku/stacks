/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Abelian
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Restriction
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.TensorExtension

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor.TensorAdeq

/-- Tensor extension of an `A`-module is tensor-adequate as a module-valued functor. -/
theorem tensorExtension_adequate (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    TensorAdequate ((tensorExtensionFunctor A).obj M) := sorry

/-- Tensor extension, lifted to the full subcategory of tensor-adequate module-valued
functors. -/
noncomputable def tensorExtension (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ TensorAdeq A :=
  ObjectProperty.lift (TensorAdequate (A := A)) (tensorExtensionFunctor A)
    (tensorExtension_adequate A)

/-- The underlying object of the lifted tensor-extension functor is ordinary tensor
extension. -/
theorem tensorExtension_obj (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    ((tensorExtension A).obj M).obj = (tensorExtensionFunctor A).obj M := sorry

/-- The underlying morphism of the lifted tensor-extension functor is ordinary tensor
extension. -/
theorem tensorExtension_map (A : CommRingCat.{u}) {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    ((tensorExtension A).map f).hom = (tensorExtensionFunctor A).map f := sorry

/-- The full subcategory of tensor-adequate module-valued functors is preadditive. -/
noncomputable def tensorAdeqPreadditive (A : CommRingCat.{u}) :
    Preadditive (TensorAdeq A) :=
  @Preadditive.fullSubcategory (bundled.{u, u} A) _ (bundledPreadditive A)
    (TensorAdequate (A := A))

/-- Tensor extension into tensor-adequate module-valued functors is additive. -/
theorem tensorExtensionAdditive (A : CommRingCat.{u})
    [Preadditive (TensorAdeq A)] :
    (tensorExtension A).Additive := sorry

end ModuleValuedFunctor.TensorAdeq
