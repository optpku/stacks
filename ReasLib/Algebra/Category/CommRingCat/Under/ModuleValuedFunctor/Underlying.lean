module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Category
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.TensorExtension

@[expose] public section

open CategoryTheory Opposite

universe u v

namespace ModuleValuedFunctor

/--
The functor taking a module-valued functor to its underlying
`AddCommGrpCat`-valued functor.
-/
noncomputable def forget (A : CommRingCat.{u}) :
    bundled.{u, v} A ⥤ (Under A ⥤ AddCommGrpCat.{v}) where
  obj F := F.toFunctor
  map φ := φ.toNatTrans
  map_id := sorry
  map_comp := sorry

/--
The object map of `forget` is `ModuleValuedFunctor.toFunctor`.
-/
theorem forget_obj (A : CommRingCat.{u}) (F : ModuleValuedFunctor.{u, v} A) :
    (forget A).obj F = F.toFunctor := sorry

/--
The components of the morphism map of `forget` are the underlying additive maps.
-/
theorem forget_map_app (A : CommRingCat.{u}) {F G : ModuleValuedFunctor.{u, v} A}
    (φ : Hom F G) (B : Under A) :
    ((forget A).map φ).app B =
      (forget₂ (ModuleCat.{v} B.right) AddCommGrpCat.{v}).map (φ.app B) := sorry

/--
The ordinary functor-valued view of the tensor-extension construction.
-/
noncomputable def tensorExtensionUnderlying (A : CommRingCat.{u}) :
    ModuleCat.{u} A ⥤ (Under A ⥤ AddCommGrpCat.{u}) :=
  tensorExtensionFunctor A ⋙ forget A

/--
The tensor-extension underlying view evaluates to the underlying functor of the
bundled tensor-extension construction.
-/
theorem tensorExtensionUnderlying_obj (A : CommRingCat.{u}) (M : ModuleCat.{u} A) :
    (tensorExtensionUnderlying A).obj M =
      ((tensorExtensionFunctor A).obj M).toFunctor := sorry

end ModuleValuedFunctor
