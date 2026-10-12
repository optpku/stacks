/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Flat

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Pointwise relative flatness of a scheme module is transitive along a morphism that is flat at
the intermediate image. -/
theorem flatOverAt_trans
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (ℱ : X.Modules) (x : X)
    (hℱ : flatOverAt ℱ f x) (hY : Scheme.Hom.flatAt g (f.base x)) :
    flatOverAt ℱ (f ≫ g) x := by
  change @Module.Flat _ (SheafOfModules.targetStalkModule ℱ (f ≫ g).toShHom x) _ _
    (ModuleCat.isModule (SheafOfModules.targetStalkModule ℱ (f ≫ g).toShHom x))
  exact
    @Module.Flat.trans _ _ (SheafOfModules.targetStalkModule ℱ (f ≫ g).toShHom x) _ _
      ((g.stalkMap (f.base x)).hom.toAlgebra) _
      (ModuleCat.isModule (SheafOfModules.targetStalkModule ℱ (f ≫ g).toShHom x))
      (ModuleCat.isModule (SheafOfModules.targetStalkModule ℱ f.toShHom x))
      (@IsScalarTower.mk _ _ _ ((g.stalkMap (f.base x)).hom.toAlgebra.toSMul)
        (ModuleCat.isModule
          (SheafOfModules.targetStalkModule ℱ f.toShHom x)).toDistribMulAction.toSMul
        (ModuleCat.isModule
          (SheafOfModules.targetStalkModule ℱ (f ≫ g).toShHom x)).toDistribMulAction.toSMul
        (fun r s m => by
          change
            (f.stalkMap x).hom ((g.stalkMap (f.base x)).hom r * s) • m =
              ((f ≫ g).stalkMap x).hom r • (f.stalkMap x).hom s • m
          rw [map_mul, Scheme.Hom.stalkMap_comp, mul_smul]
          rfl))
      hY hℱ

end AlgebraicGeometry.Scheme.Modules
