module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Tensor.Connectivity
import StacksCheckRecall

/-!
# Induced maps after derived tensor with a sheaf

Derived tensoring with a module sheaf preserves both upper cohomological connectivity
conditions for maps between bounded-above derived module objects.
-/

@[expose] public section

open CategoryTheory DerivedCategory
open SheafOfModules.RingedSite (ringedSiteModuleCategory)
open RingedSite.Hom (ModuleDerived)
open RingedSite.Hom.ModuleDerived (cohomologySheafMap tensorRightHom)

noncomputable section

universe u v w

-- Local instance justification (defeq pin): the complete expected types use the same
-- standard derived-category model as `ModuleDerived` and the canonical tensor owner.
-- `moduleCategoryHasDerivedCategory` unfolds to `moduleCat_hasDerivedCategory` at
-- `ofCommRingSheaf J O`; its site-indexed head lets instance synthesis recover J and O.
-- Local instance justification (defeq pin): the site-indexed standard model aligns ModuleDerived, cohomologySheafMap, singleFunctor, and derived tensoring while recovering J and O.
attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasDerivedCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [UnivLE.{max u v, w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (O : Sheaf J CommRingCat.{w})

/- Lemma 91.16.3 (1): derived tensor with a module sheaf preserves cohomological
isomorphisms in degrees at least n for morphisms in D⁻(𝒪). -/
@[stacks 0DIV] #check
  (RingedSite.Hom.ModuleDerived.derivedTensor_homologyMap_isIso O :
    ∀ {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)},
      IsBoundedAbove K → IsBoundedAbove L →
      ∀ (α : K ⟶ L) (F : ringedSiteModuleCategory.{u, v, w, w} J O) (n : ℤ),
        (∀ j, n ≤ j → IsIso (cohomologySheafMap (RingedSite.ofCommRingSheaf J O) j α)) →
        ∀ i, n ≤ i →
          IsIso (cohomologySheafMap (RingedSite.ofCommRingSheaf J O) i
            (tensorRightHom O F α)))

/- Lemma 91.16.3 (2): derived tensor with a module sheaf preserves cohomological
isomorphisms above n and an epimorphism at n for morphisms in D⁻(𝒪). -/
@[stacks 0DIV] #check
  (RingedSite.Hom.ModuleDerived.derivedTensor_homologyMap_isIso_and_epi O :
    ∀ {K L : ModuleDerived.{w} (RingedSite.ofCommRingSheaf J O)},
      IsBoundedAbove K → IsBoundedAbove L →
      ∀ (α : K ⟶ L) (F : ringedSiteModuleCategory.{u, v, w, w} J O) (n : ℤ),
        (∀ j, n < j → IsIso (cohomologySheafMap (RingedSite.ofCommRingSheaf J O) j α)) →
        Epi (cohomologySheafMap (RingedSite.ofCommRingSheaf J O) n α) →
        (∀ i, n < i → IsIso (cohomologySheafMap (RingedSite.ofCommRingSheaf J O) i
          (tensorRightHom O F α))) ∧
          Epi (cohomologySheafMap (RingedSite.ofCommRingSheaf J O) n
            (tensorRightHom O F α)))
