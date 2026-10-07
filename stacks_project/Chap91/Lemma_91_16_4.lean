module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.ChangeOfRings
public import stacks_project.Chap91.Lemma_91_16_2_CanonicalClass
import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing of the canonical class of a complex on a square-zero ringed site

On a site, for a locally surjective square-zero map `π : 𝒪 ⟶ 𝒪₀` of ring sheaves with kernel
ideal sheaf `ℐ`, and for every `K₀` in `D⁻(𝒪₀)`, the canonical class `ω(K₀)` from Lemma 91.16.2
vanishes if and only if `K₀` lifts to an object of `D⁻(𝒪)`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open DerivedCategory
open RingedSite (ModuleCat)
open RingedSite.Hom (ModuleDerived)
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.SameSite (pullbackDerived)
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u v w

namespace RingedSite.Hom.ModuleDerived

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and `DerivedTensor.Right.functor` must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory
-- Local instance justification (defeq pin): `moduleMonoidalCategory` is the tensor used by `unitIsoTensorUnit`, whiskering, and `λ_`; it must agree with module-level tensors on `ringedSiteModuleCategory`.
attribute [local instance] SheafOfModules.RingedSite.moduleMonoidalCategory
-- Local instance justification (defeq pin): `moduleSymmetricCategory` supplies the braiding `I ⊗ F ≅ F ⊗ I` used to place the kernel ideal on the right in the cochain components of `ω`.
attribute [local instance] SheafOfModules.RingedSite.moduleSymmetricCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]
variable {𝒪 𝒪₀ : Sheaf J CommRingCat.{w}}
variable (π : 𝒪 ⟶ 𝒪₀)
variable [Sheaf.IsLocallySurjective π]
variable [(restrictionAlong π).IsRightAdjoint]
variable (h_sq : KernelIdeal.IsSquareZero π)
variable [SheafOfModules.Localization.HasLowerShriek.{w} (ringSheaf J 𝒪)]
variable [CategoryTheory.Limits.HasCoproducts.{max u w}
  (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))]
variable [CategoryTheory.Limits.HasZeroObject
  (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))]
variable [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))]
variable [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))]
variable [∀ K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ,
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))) (up ℤ)]
variable [@DerivedTensor.Right.Has
    (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
variable [@DerivedTensor.Bifunctor.Has
    (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _ _ _ _ _]
variable [(restrictionAlong π).LaxMonoidal]

/-- Lemma 91.16.4: Let `C` be a site. Let `π : 𝒪 ⟶ 𝒪₀` be a surjection of sheaves of rings
whose kernel is an ideal sheaf `ℐ` of square zero. For every object `K₀` in `D⁻(𝒪₀)`, the
class `ω(K₀) : K₀ ⟶ (K₀ ⊗ᴸ ℐ[0])⟦2⟧` in `D(𝒪₀)` from Lemma 91.16.2 (the Hom-form of the
class in `Ext⁽2⁾(K₀, K₀ ⊗_{𝒪₀} ℐ)`) vanishes if and only if there exists `K` in `D⁻(𝒪)`
with `(pullbackDerived π).obj K` isomorphic to `K₀` in `D(𝒪₀)`. -/
@[stacks 0DIW]
theorem canonicalClass_eq_zero_iff
    (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))
    (hK : K₀.IsBoundedAbove) :
    canonicalClass π h_sq K₀ hK = 0 ↔
      ∃ K : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪),
        K.IsBoundedAbove ∧
          IsIsomorphic ((pullbackDerived π).obj K) K₀ := sorry

end RingedSite.Hom.ModuleDerived
