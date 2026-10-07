module

public import stacks_project.Chap91.Lemma_91_16_7_IsoClass
public import stacks_project.Chap91.Lemma_91_16_7_Lift
import Mathlib.Tactic.CrossRefAttribute

/-!
# Automorphisms and isomorphism classes of first-order lifts of complexes

On a site, for a locally surjective square-zero map `π : 𝒪 ⟶ 𝒪₀` of ring sheaves with kernel
ideal `ℐ`, a lift of `K₀` in `D⁻(𝒪₀)` is a pair `(K, α₀)` with `K` in `D⁻(𝒪)` and
`α₀ : K ⊗ᴸ 𝒪₀ ≅ K₀` in `D(𝒪₀)`. Automorphisms of a given lift are the cokernel of a canonical
map `Ext⁽-1⁾(K₀, K₀) → Hom(K₀, K₀ ⊗ᴸ ℐ)`. If a lift exists, isomorphism classes of lifts are
a principal homogeneous space under `Ext⁽1⁾(K₀, K₀ ⊗ᴸ ℐ)`.
-/

@[expose] public section

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

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [J.WEqualsLocallyBijective CommRingCat.{w}]

variable {𝒪 𝒪₀ : Sheaf J CommRingCat.{w}} (π : 𝒪 ⟶ 𝒪₀)
variable [Sheaf.IsLocallySurjective π]
variable (h_sq : KernelIdeal.IsSquareZero π)
variable [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))]
variable [MonoidalPreadditive (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))]
variable [∀ K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) ℤ,
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))) (up ℤ)]
variable [∀ K L : CochainComplex (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) ℤ,
  HomologicalComplex.HasMapBifunctor K L
    (curriedTensor (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))) (up ℤ)]
variable [@DerivedTensor.Right.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) _ _ _ _ _ _]
variable [@DerivedTensor.Left.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)) _ _ _ _ _ _]
variable [@DerivedTensor.Right.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
variable [@DerivedTensor.Left.Has (ModuleCat.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)) _ _ _ _ _ _]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{w} (sameSiteHom π))
  (ModuleQis.{w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))]
variable [DerivedAdjunction.HasPair.{w} (sameSiteHom π)]
variable [KFlat.HomotopyTensorDescends 𝒪]
variable [KFlat.TensorDescends 𝒪]
variable [KFlat.IsLocalization 𝒪]
variable [KFlat.HomotopyTensorDescends 𝒪₀]
variable [KFlat.TensorDescends 𝒪₀]
variable [KFlat.IsLocalization 𝒪₀]
variable [Tensor.Has 𝒪₀]
variable [(tensorO0 π).OplaxMonoidal]
variable [(pushforwardO0 π).CommShift ℤ]
variable [∀ (L : ModuleDerived.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪)), (tensorLeft L).CommShift ℤ]
variable [∀ (L : ModuleDerived.{w, u, v, w}
    (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪))
    (M : ModuleDerived.{w, u, v, w}
      (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀)),
  IsIso ((moduleDerivedAdjunction.{w} (sameSiteHom π)).projectionFormulaMate L M)]
variable [IsIso (pushforwardSingleUnit π (unitModule J 𝒪₀))]

variable (K₀ : ModuleDerived.{w, u, v, w} (RingedSite.ofCommRingSheaf.{u, v, w} J 𝒪₀))

/-- Lemma 91.16.7 (1): Let `C` be a site. Let `π : 𝒪 ⟶ 𝒪₀` be a surjection of sheaves of rings
whose kernel is an ideal sheaf `ℐ` of square zero. Let `K₀` be an object of `D⁻(𝒪₀)`, and let
`(K, α₀)` be a lift of `K₀`. The group of automorphisms of the pair is canonically the cokernel
of the map `Ext⁽-1⁾_{𝒪₀}(K₀, K₀) ⟶ Hom_{𝒪₀}(K₀, K₀ ⊗ᴸ ℐ)`. -/
@[stacks 0DIZ]
noncomputable def autEquiv (L : Lift π h_sq K₀) (hK : K₀.IsBoundedAbove) :
    autCoker π h_sq L ≃ Aut π h_sq L :=
  Equiv.ofBijective (ofCoker π h_sq L) (ofCoker_bijective π h_sq L hK)

/-- The forward map of `autEquiv` is `ofCoker`. -/
theorem autEquiv_apply (L : Lift π h_sq K₀) (hK : K₀.IsBoundedAbove)
    (x : autCoker π h_sq L) :
    autEquiv π h_sq K₀ L hK x = ofCoker π h_sq L x := sorry

/-- Lemma 91.16.7 (2): If there is a lift of `K₀`, then the set of isomorphism classes of lifts
is principal homogeneous under `Ext⁽1⁾_{𝒪₀}(K₀, K₀ ⊗ᴸ ℐ)`, via the obstruction class of
Lemma 91.16.6. -/
@[stacks 0DIZ]
theorem isoClass_extClass_bijective (hK : K₀.IsBoundedAbove) (L0 : Lift π h_sq K₀) :
    Function.Bijective (extClass π h_sq K₀ L0 hK) := sorry

end RingedSite.Hom.ModuleDerived
