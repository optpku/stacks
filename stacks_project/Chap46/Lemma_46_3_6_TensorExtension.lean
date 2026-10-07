module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.TensorExtension
public import stacks_project.Chap46.Definition_46_3_2_Instances

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor

/-- The tensor-extension functor sending an `A`-module `M` to the module-valued
functor `B ↦ B ⊗[A] M`, with transition maps induced by morphisms of `A`-algebras. -/
noncomputable def tensorExtension (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ ModuleValuedFunctor.{u, u} A where
  obj M := tensorExtensionObj A M
  map f := tensorExtensionMap A f
  map_id M := tensorExtensionMap_id A M
  map_comp f g := tensorExtensionMap_comp A f g

/-- Evaluating `tensorExtension A` at `M` and then at an `A`-algebra `B` gives
the canonical extension of scalars `B ⊗[A] M`. -/
theorem tensorExtension_obj_obj (A : CommRingCat.{u}) (M : ModuleCat.{u} A)
    (B : Under A) :
    ((tensorExtension A).obj M).obj B =
      (ModuleCat.extendScalars B.hom.hom).obj M :=
  tensorExtensionFunctor_obj_obj A M B

end ModuleValuedFunctor
