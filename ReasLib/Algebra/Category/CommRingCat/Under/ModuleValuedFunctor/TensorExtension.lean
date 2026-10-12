/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.Under.Basic
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Category

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor

/-- Extension of scalars sends an `A`-module `M` to the module-valued functor
whose value at an `A`-algebra `B` is `B ⊗[A] M`. -/
noncomputable def tensorExtensionObj (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    ModuleValuedFunctor.{u, u} A where
  obj B := (ModuleCat.extendScalars B.hom.hom).obj M
  map {B B'} f :=
    ModuleCat.semilinearMapAddEquiv f.right.hom _ _
      { toFun := fun x ↦ TensorProduct.map
            (CommRingCat.toAlgHom f).toLinearMap LinearMap.id x
        map_add' := sorry
        map_smul' := sorry }
  map_id := sorry
  map_comp := sorry

/-- An `A`-linear map induces a morphism between the corresponding
extension-of-scalars module-valued functors. -/
noncomputable def tensorExtensionMap (A : CommRingCat.{u})
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    Hom (tensorExtensionObj A M) (tensorExtensionObj A N) where
  app B := (ModuleCat.extendScalars B.hom.hom).map f
  naturality := sorry

/-- Tensor extension sends identity maps to identity morphisms. -/
theorem tensorExtensionMap_id (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    tensorExtensionMap A (𝟙 M) = Hom.id (tensorExtensionObj A M) := sorry

/-- Tensor extension sends composites to composites. -/
theorem tensorExtensionMap_comp (A : CommRingCat.{u}) {M N P : ModuleCat.{u} A}
    (f : M ⟶ N) (g : N ⟶ P) :
    tensorExtensionMap A (f ≫ g) =
      Hom.comp (tensorExtensionMap A f) (tensorExtensionMap A g) := sorry

/-- Extension of scalars as a functor from `A`-modules to the bundled category
of module-valued functors on `A`-algebras. -/
noncomputable def tensorExtensionFunctor (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ bundled.{u, u} A where
  obj M := tensorExtensionObj A M
  map f := tensorExtensionMap A f
  map_id M := tensorExtensionMap_id A M
  map_comp f g := tensorExtensionMap_comp A f g

/-- Evaluating tensor extension at `M` and then at an `A`-algebra `B` gives
the canonical extension of scalars `B ⊗[A] M`. -/
theorem tensorExtensionFunctor_obj_obj (A : CommRingCat.{u}) (M : ModuleCat.{u} A)
    (B : Under A) :
    ((tensorExtensionFunctor A).obj M).obj B =
      (ModuleCat.extendScalars B.hom.hom).obj M := sorry

end ModuleValuedFunctor
