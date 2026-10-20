module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.MapObstruction
import StacksCheckRecall

/-!
# Obstruction to lifting a map of complexes along a square-zero surjection

On a site, a map `α₀ : K₀ ⟶ L₀` in `D(𝒪₀)` obtained by derived tensor with a square-zero
quotient of ring sheaves lifts to a map in `D(𝒪)` if and only if its canonical obstruction
class in `Ext⁽1⁾` vanishes.
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

/- Lemma 91.16.6: Let `C` be a site. Let `π : 𝒪 ⟶ 𝒪₀` be a surjection of sheaves of rings
whose kernel is an ideal sheaf `ℐ` of square zero. Let `K, L` be objects of `D⁻(𝒪)`, and set
`K₀ = K ⊗ᴸ 𝒪₀` and `L₀ = L ⊗ᴸ 𝒪₀` in `D⁻(𝒪₀)`. Given `α₀ : K₀ ⟶ L₀` in `D(𝒪₀)` there is a
canonical element `o(α₀)` in `Ext⁽1⁾(K₀, L₀ ⊗ᴸ ℐ)` whose vanishing is necessary and sufficient
for the existence of a map `α : K ⟶ L` in `D(𝒪)` with `α₀ = α ⊗ᴸ id`. The class `o(α₀)` is
`mapObstruction π h_sq α₀`, and `α ⊗ᴸ id` is `(tensorO0 π).map α`. -/
@[stacks 0DIY] #check (RingedSite.Hom.ModuleDerived.mapObstruction_eq_zero_iff :
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
      {a b : ℤ} [K.IsLE a] [L.IsLE b]
      (α₀ : (tensorO0 π).obj K ⟶ (tensorO0 π).obj L),
      mapObstruction π h_sq α₀ = 0 ↔
        ∃ α : K ⟶ L, (tensorO0 π).map α = α₀)

end RingedSite.Hom.ModuleDerived
