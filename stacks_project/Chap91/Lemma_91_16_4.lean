module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Obstruction
import StacksCheckRecall

/-!
# Vanishing of the canonical class of a complex on a square-zero ringed site

On a site, for a locally surjective square-zero map `π : 𝒪 ⟶ 𝒪₀` of ring sheaves with kernel
ideal sheaf `ℐ`, and for every `K₀` in `D⁻(𝒪₀)`, the canonical class `ω(K₀)` from Lemma 91.16.2
vanishes if and only if `K₀` lifts to an object of `D⁻(𝒪)`.
-/

@[expose] public section

open CategoryTheory
open DerivedCategory
open RingedSite.Hom.ModuleDerived
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.SameSite (pullbackDerived)

noncomputable section

universe u v w

-- Local instance justification (defeq pin): this pins free HasDerivedCategory inference to the standard model already fixed by RingedSiteDerived and canonicalClass.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

/- Lemma 91.16.4: Let `C` be a site. Let `π : 𝒪 ⟶ 𝒪₀` be a surjection of sheaves of rings
whose kernel is an ideal sheaf `ℐ` of square zero. For every object `K₀` in `D⁻(𝒪₀)`, the
class `ω(K₀) : K₀ ⟶ (K₀ ⊗ᴸ ℐ[0])⟦2⟧` in `D(𝒪₀)` from Lemma 91.16.2 (the Hom-form of the
class in `Ext⁽2⁾(K₀, K₀ ⊗_{𝒪₀} ℐ)`) vanishes if and only if there exists `K` in `D⁻(𝒪)`
with `(pullbackDerived π).obj K` isomorphic to `K₀` in `D(𝒪₀)`. -/
@[stacks 0DIW] #check (RingedSite.Hom.ModuleDerived.canonicalClass_eq_zero_iff :
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
      canonicalClass π h_sq K₀ hK = 0 ↔
        ∃ K : RingedSiteDerived.{u, v, w, w} J 𝒪,
          K.IsBoundedAbove ∧ IsIsomorphic ((pullbackDerived π).obj K) K₀)
