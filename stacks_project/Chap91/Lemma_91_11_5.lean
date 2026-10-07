module

public import stacks_project.Chap91.Lemma_91_11_1_Lift
public import stacks_project.Chap91.Lemma_91_11_5_Obstruction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Obstruction to lifting a module map on a first-order thickening of ringed topoi

On a first-order thickening of ringed topoi, an 𝒪-linear map φ : i^* ℱ' ⟶ i^* 𝒢' lifts to an
𝒪'-linear map ℱ' ⟶ 𝒢' if and only if its canonical class in Ext⁽1⁾(Li^* ℱ', ℐ 𝒢') vanishes.
-/

@[expose] public section

open CategoryTheory
open DerivedCategory
open RingedSite.Hom
open SheafOfModules.RingedSite
open scoped DerivedExt

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

-- Local instance justification (defeq pin): `moduleCat_hasDerivedCategory` is reducible to `HasDerivedCategory.standard` and is not global; `ModuleDerived`, `singleFunctor`, and `moduleDerivedAdjunction` must share that same derived-category instance.
attribute [local instance] RingedSite.Hom.moduleCat_hasDerivedCategory
-- Local instance justification (defeq pin): the commutative-sheaf presentation uses the same standard derived-category owner, exposed through the site-level spelling.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable [UnivLE.{max u v, max u v}]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable [IsFirstOrderThickening π]
variable [(SheafOfModules.restrictScalars (ringSheafMap π)).IsRightAdjoint]
variable [Functor.HasRightDerivedFunctor
  (modulePushforwardToDerived.{max u v} (sameSiteHom π))
  (ModuleQis.{max u v} (RingedSite.ofCommRingSheaf J 𝒪))]
variable [DerivedAdjunction.HasPair.{max u v} (sameSiteHom π)]
variable [(modulePushforwardDerived (sameSiteHom π)).CommShift ℤ]
variable (F' G' : ringedSiteModuleCategory.{u, v, max u v, max u v} J 𝒪')
variable (φ : (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj F' ⟶
    (SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap π)).obj G')

/-- Lemma 91.11.5: Let i : (Sh(C), 𝒪) ⟶ (Sh(D), 𝒪') be a first-order thickening of ringed
topoi. Let ℱ', 𝒢' be 𝒪'-modules and set ℱ = i^* ℱ' and 𝒢 = i^* 𝒢'. Let φ : ℱ ⟶ 𝒢 be an
𝒪-linear map. There exists an element o(φ) ∈ Ext⁽1⁾_𝒪(Li^* ℱ', ℐ 𝒢') whose vanishing is a
necessary and sufficient condition for the existence of a lift of φ to an 𝒪'-linear map
φ' : ℱ' ⟶ 𝒢'. -/
@[stacks 08MS]
theorem liftObstruction_eq_zero_iff :
    liftObstruction π F' G' φ = 0 ↔ Nonempty (Lift F' G' φ) :=
  sorry

end SheafOfModules.RingedSite.FirstOrderThickening
