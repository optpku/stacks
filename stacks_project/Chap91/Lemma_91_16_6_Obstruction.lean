module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.MapObstruction

/-!
# Obstruction class of a map of complexes along a square-zero kernel

The canonical class of a map between derived reductions is the adjunction mate of the
composite with the connecting morphism of the square-zero kernel sequence.
-/

public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open DerivedCategory
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived)
open SheafOfModules.RingedSite
open scoped CategoryTheory.DerivedCategory.DerivedTensor
open scoped DerivedExt

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, `DerivedTensor.Right.functor`, and `moduleDerivedAdjunction` must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): `monoidalCategory` is reducible to `KFlat.monoidalCategory` at the pinned `moduleCat_hasDerivedCategory`; `ρ_`, whiskering, `tensorLeft`, `mapUnitIso`, and the Ext target of `mapObstruction` must share that tensor.
attribute [local instance] monoidalCategory

/- Lemma 91.16.6: The canonical obstruction class of a map between derived reductions lies in
the degree-one Ext group with coefficients in the derived tensor with the kernel ideal. -/
#check (RingedSite.Hom.ModuleDerived.mapObstruction :
  ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [UnivLE.{max u v, w}]
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J CommRingCat.{w}]
    [J.WEqualsLocallyBijective CommRingCat.{w}]
    {𝒪 𝒪₀ : Sheaf J CommRingCat.{w}} (π : 𝒪 ⟶ 𝒪₀)
    [Sheaf.IsLocallySurjective π]
    (h_sq : KernelIdeal.IsSquareZero π)
    [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))]
    [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))]
    [∀ K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))) (up ℤ)]
    [∀ K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ,
      HomologicalComplex.HasMapBifunctor K L
        (curriedTensor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))) (up ℤ)]
    [@DerivedTensor.Right.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) _ _ _ _ _ _]
    [@DerivedTensor.Left.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) _ _ _ _ _ _]
    [@DerivedTensor.Right.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
    [@DerivedTensor.Left.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
    [Functor.HasRightDerivedFunctor
      (modulePushforwardToDerived.{w} (sameSiteHom π))
      (ModuleQis.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))]
    [DerivedAdjunction.HasPair.{w} (sameSiteHom π)]
    [KFlat.HomotopyTensorDescends 𝒪]
    [KFlat.TensorDescends 𝒪]
    [KFlat.IsLocalization 𝒪]
    [KFlat.HomotopyTensorDescends 𝒪₀]
    [KFlat.TensorDescends 𝒪₀]
    [KFlat.IsLocalization 𝒪₀]
    [Tensor.Has 𝒪₀]
    [(tensorO0 π).OplaxMonoidal]
    [(pushforwardO0 π).CommShift ℤ]
    [∀ (L : ModuleDerived.{w, u, v, w}
        (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)), (tensorLeft L).CommShift ℤ]
    [∀ (L : ModuleDerived.{w, u, v, w}
        (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
        (M : ModuleDerived.{w, u, v, w}
          (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)),
      IsIso ((moduleDerivedAdjunction.{w} (sameSiteHom π)).projectionFormulaMate L M)]
    [IsIso (pushforwardSingleUnit π (unitModule J 𝒪₀))]
    {K L : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)}
    (α₀ : (tensorO0 π).obj K ⟶ (tensorO0 π).obj L),
    Ext⁽(1 : ℤ)⁾((tensorO0 π).obj K,
      (tensorO0 π).obj L ⊗ kernelIdeal0Single π h_sq))

end RingedSite.Hom.ModuleDerived
