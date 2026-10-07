module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor
import StacksCheckRecall

@[expose] public section

/- Definition 21.17.13 (06YU): for a fixed object `F` of the derived category of module sheaves
on a commutative ringed site, `DerivedTensor.Right.functor F` is the exact functor
`K ↦ K ⊗ᴸ F`.  Its counit records the total-left-derived universal property. -/

open CategoryTheory ComplexShape

noncomputable section

universe u v w

@[stacks 06YU]
#check @DerivedCategory.DerivedTensor.Right.functor

#check @DerivedCategory.DerivedTensor.Right.obj
#check @DerivedCategory.DerivedTensor.Right.counit
#check @DerivedCategory.DerivedTensor.Right.commShift
#check @Functor.totalLeftDerived_isTriangulated
#check @SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor

namespace RingedSite.Hom.ModuleDerived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [UnivLE.{max u v, w}]
variable (O : Sheaf J CommRingCat.{w})
variable [DerivedCategory.DerivedTensor.Right.Has
  (C := ModuleCat.{w} (RingedSite.ofCommRingSheaf J O))]
variable (F : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O))

#check DerivedCategory.DerivedTensor.Right.functor F
#check DerivedCategory.DerivedTensor.Right.obj F
#synth (DerivedCategory.DerivedTensor.Right.functor F).CommShift ℤ
#synth (DerivedCategory.DerivedTensor.Right.functor F).IsTriangulated

end RingedSite.Hom.ModuleDerived

end
