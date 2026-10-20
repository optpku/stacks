module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CanonicalClass
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open DerivedCategory
open SheafOfModules.RingedSite
open RingedSite.Hom.ModuleDerived

noncomputable section

universe u v w

-- Local instance justification (defeq pin): RingedSiteDerived fixes the standard derived category, while Q, singleFunctor, and the derived-tensor interfaces have a free HasDerivedCategory parameter; this registration selects that same standard presentation.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

/- Lemma 91.16.2 (existence): a locally surjective square-zero ring-sheaf morphism
canonically gives each bounded-above derived module its degree-two obstruction. -/
@[stacks 0DIU] #check (RingedSite.Hom.ModuleDerived.canonicalClass :
    ∀ {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
      [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
      [UnivLE.{max u v, w}]
      [HasWeakSheafify J AddCommGrpCat.{w}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
      [HasWeakSheafify J CommRingCat.{w}]
      [J.WEqualsLocallyBijective CommRingCat.{w}]
      {𝒪 𝒪₀ : Sheaf J CommRingCat.{w}} (π : 𝒪 ⟶ 𝒪₀)
      [Sheaf.IsLocallySurjective π]
      [(restrictionAlong π).IsRightAdjoint]
      (h_sq : KernelIdeal.IsSquareZero π)
      [SheafOfModules.Localization.HasLowerShriek.{w} (ringSheaf J 𝒪)]
      [DerivedTensor.Right.Has (C := ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀)]
      [DerivedTensor.Bifunctor.Has (C := ringedSiteModuleCategory.{u, v, w, w} J 𝒪₀)]
      (K₀ : RingedSiteDerived.{u, v, w, w} J 𝒪₀) (hK : K₀.IsBoundedAbove),
      K₀ ⟶ tensorKernelShift π h_sq K₀)
